{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Disorder.FSM (
  -- * Transition type and constructor
    Transition
  , mkTransition
  , ask
  , get
  , put
  , modify
  -- * Combinators to make 'Transition' less trivial
  , goif
  , goto
  -- * Stubs for combinators arguments
  , always
  , sameState
  -- * Helpers
  , liftGen
  , assert
  , (===)
  -- * Transition evaluation
  , runFSM
  , runFSMCont
  ) where

import           Prelude (Show(..))
import           Data.Bool
import           Data.Eq
import           Data.String
import           Data.Tuple
import           Data.Function
import           Data.Monoid
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.Cont
import           Control.Monad.Trans.Cont
import           Control.Monad.RWS.Strict hiding (state)

import           Test.QuickCheck.Arbitrary
import           Test.QuickCheck.Gen
import           Test.QuickCheck.Modifiers
import           Test.QuickCheck.Monadic hiding (assert)
import           Test.QuickCheck.Property hiding ((===))


-- | Defines a transition from state to state
data Transition e s m = MkTransition {
    -- | Display name (used in case of failure)
    name :: String
    -- | Indicates is this transition is applicable for a given environment 'e' and state 's'
  , preCond :: s -> Bool -- Precondition e s m Bool
    -- | Transition action
  , transition :: Action e s m ()
  }

newtype Action e s m p = Action {
    runAction :: RWST e String s (PropertyM m) p
  } deriving (
    Functor
  , Monad
  , MonadReader e
  , MonadState s
  , MonadIO
  )

instance MonadTrans (Action e s) where
  lift = Action . lift . lift

instance Show (Transition e s m) where
  show = name

-- | Constructor for 'Transition'
--   Create unconditional 'Transition' which does nothing
mkTransition :: (Monad m) => String -> Transition e s m
mkTransition name' = MkTransition name' always sameState

-- | Define condition to 'Transition'
goif :: Transition e s m -> (s -> Bool) -> Transition e s m
goif t preCond' = t { preCond = preCond' }

-- | Define transition logic
goto :: Transition e s m -> Action e s m () -> Transition e s m
goto t transition' = t { transition = transition' }

-- | Do not change the state or eval any monadic actions
sameState :: Monad m => Action e s m ()
sameState = return ()

-- | Make 'Transition' unconditional
always :: s -> Bool
always = const True

-- | Lift generator to 'Action'
liftGen :: (Monad m, Show a) => Gen a -> Action e s m a
liftGen g = Action . lift . pick $ g

-- | FSM implementation of QC 'assert'
assert :: Monad m => Bool -> Action e s m ()
assert c =
  unless c $ fail "Assertion failed"

-- | FSM implementation of QC '(===)'
infix 4 ===
(===) :: (Eq a, Show a, Monad m) => a -> a -> Action e s m ()
x === y =
  unless (x == y) $ fail (show x <> " /= " <> show y)


-- | Similar to 'runFSM' but can be used with 'ContT' monad
--   'ContT' does not define 'MonadCatch' instance, so it it cannot be passed to 'runFSM'
runFSMCont :: (MonadCatch m, Show s) => r -> s -> Gen (Transition r s (ContT Property m)) -> PropertyM (ContT Property m) ()
runFSMCont env state g = do
  Positive n <- pick arbitrary
  return . fst =<< evalRWST (replicateM_ n go) env (state, "")
  where
    go = do
      (s, _) <- get
      t <- lift . pick $ g `suchThat` flip preCond s
      modify $ \(s', ss') -> (s', ss' <> formatState t s)
      let m = RWST $ \r (s', ss') -> do
           (a'', s'', w'') <- runRWST (runAction (transition t)) r s'
           return (a'', (s'', ss'), w'')
      m `handleE` handleException

    handleE (RWST m) h = RWST $ \r s@(_, w) ->
      m r s `catchPropCont` \e -> runRWST (h e w) r s

    handleException (e :: SomeException) s = fail $ s <> "Exception thrown: " <> show e

    formatState t s = "\n(" <> show s <> ") -> " <> name t <> " -> "


runFSM :: (Show s, MonadCatch m) => e -> s -> Gen (Transition e s m) -> PropertyM m ()
runFSM env state g =
  let pm = runFSMCont env state $ do
        MkTransition n p a <- g
        return $ MkTransition n p $
            (Action . RWST) $ \r s ->
              MkPropertyM $ \h ->
                let h' = (fmap evalContT) . h
                in unPropertyM (runRWST (runAction a) r s) h' >>= return . lift

  in MkPropertyM $ \ h -> do
    let h' = fmap lift . h
    unPropertyM pm h' >>= return . evalContT


catchPropCont :: (Exception e, MonadCatch m) =>
  PropertyM (ContT Property m) a -> (e -> PropertyM (ContT Property m) a) -> PropertyM (ContT Property m) a
catchPropCont (MkPropertyM f) g = MkPropertyM $ \h -> catchGenCont (f h) (\e -> unPropertyM (g e) h)

catchGenCont :: (Exception e, MonadCatch m) => Gen (ContT r m r) -> (e -> Gen (ContT r m a)) -> Gen (ContT r m a)
catchGenCont (MkGen f) g = MkGen $ \q i -> catchCont (f q i) (\e -> unGen (g e) q i)

catchCont :: (Exception e, MonadCatch m) => ContT r m r -> (e -> ContT r m a) -> ContT r m a
catchCont m g = ContT $ \c -> (runContT m return `catch` (\e -> runContT (g e) c)) -- >>= k
