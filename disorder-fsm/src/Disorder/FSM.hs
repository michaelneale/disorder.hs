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
import           Data.Maybe
import           Data.Tuple
import           Data.Function
import           Data.Monoid
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.Cont
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
    runAction :: RWST e () s (PropertyM m) p
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

-- | Generate and execute a list of 'Transition's
--   given environment 'env' and initial state 'state'
--   For longer running 'Transition's limit the list produced by 'g'
runFSM :: (Show s, MonadCatch m) => e -> s -> Gen (Transition e s m) -> PropertyM m ()
runFSM env state g = do
  Positive n <- pick arbitrary
  return . fst =<< evalRWST (replicateM_ n go) env state
  where
    go = do
      s <- get
      t <- lift . pick $ g `suchThat` flip preCond s
      lift $ handleError t s -- add transition chain to QuickCheck error in case of failure
      (runAction . transition $ t) `catchTran` handleException -- run transition with additional handling

    handleException (e :: SomeException) = fail $ "Exception thrown: " <> show e

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
      lift $ handleError t s -- add transition chain to QuickCheck error in case of failure
      modify $ \(s', ss') -> (s', ss' <> formatState t s)
      let m = RWST $ \r (s', ss') -> do
           (a'', s'', w'') <- runRWST (runAction (transition t)) r s'
           return (a'', (s'', ss'), w'')
      m `catchTranCont` handleException

    handleException (e :: SomeException) = do
     (_, ss) <- get
     fail $ ss <> "Exception thrown: " <> show e


handleError :: (Show a, Monad m) => Transition e s m -> a -> PropertyM m ()
handleError t s = monitor (mapTotalResult (addFailureReason t s))

addFailureReason :: Show a => Transition e s m -> a -> Result -> Result
addFailureReason t s = \case
 r@MkResult{ ok = Just False } -> r { reason = formatState t s <> reason r}
 r -> r

formatState :: Show a => Transition e s m -> a -> String
formatState t s = "\n(" <> show s <> ") -> " <> name t <> " -> "


-- | There is no MonadCatch instance for PropertyM so here is how it could be implemented
catchTran :: (Exception e, MonadCatch m) => RWST r w s (PropertyM m) a -> (e -> RWST r w s (PropertyM m) a) -> RWST r w s (PropertyM m) a
catchTran (RWST m) g = RWST $ \r s -> m r s `catchProp` \e -> runRWST (g e) r s

catchProp :: (Exception e, MonadCatch m) => PropertyM m a -> (e -> PropertyM m a) -> PropertyM m a
catchProp (MkPropertyM f) g = MkPropertyM $ \h -> f h `catchGen` \e -> unPropertyM (g e) h

catchGen :: (Exception e, MonadCatch m) => Gen (m a) -> (e -> Gen (m a)) -> Gen (m a)
catchGen (MkGen f) g = MkGen $ \q i -> f q i `catch` \e -> unGen (g e) q i

-- | MonadCatch implementation for RWST r w s (PropertyM (ContT Property m)) a
catchTranCont :: (Exception e, MonadCatch m) =>
  RWST r w s (PropertyM (ContT Property m)) a ->
  (e -> RWST r w s (PropertyM (ContT Property m)) a) ->
  RWST r w s (PropertyM (ContT Property m)) a
catchTranCont (RWST m) g = RWST $ \r s -> m r s `catchPropCont` \e -> (runRWST) (g e) r s

catchPropCont :: (Exception e, MonadCatch m) =>
  PropertyM (ContT Property m) a -> (e -> PropertyM (ContT Property m) a) -> PropertyM (ContT Property m) a
catchPropCont (MkPropertyM f) g = MkPropertyM $ \h -> f h `catchGenCont` \e -> unPropertyM (g e) h

catchGenCont :: (Exception e, MonadCatch m) => Gen (ContT r m a) -> (e -> Gen (ContT r m r)) -> Gen (ContT r m a)
catchGenCont (MkGen f) g = MkGen $ \q i -> f q i `catchCont` \e -> unGen (g e) q i

catchCont :: (Exception e, MonadCatch m) => ContT r m a -> (e -> ContT r m r) -> ContT r m a
catchCont m g = mapContT (`catch` ((`runContT`return) . g)) m
