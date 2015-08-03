{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
  -- * Transition evaluation
  , runFSM
--  , runFSMCont
  ) where

import           Prelude (Show(..))
import           Data.Bool
import           Data.String
import           Data.Maybe
import           Data.Tuple
import           Data.Function
import           Data.Monoid
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.Cont
import           Control.Monad.Reader (ReaderT, MonadReader(..))
import           Control.Monad.RWS.Strict -- (RWST(..), evalRWST)
import           Control.Monad.State (MonadState(get, put), modify)

import           Test.QuickCheck.Arbitrary
import           Test.QuickCheck.Gen
import           Test.QuickCheck.Monadic
import           Test.QuickCheck.Property



-- | Defines a transition from state to state
data Transition e s m p = MkTransition {
    -- | Display name (used in case of failure)
    name :: String
    -- | Indicates is this transition is applicable for a given environment 'e' and state 's'
  , preCond :: s -> Bool -- Precondition e s m Bool
    -- | Transition action
  , transition :: Action e s m p
  }

-- newtype Precondition e s m a = Precondition {
--     runPrecondition :: ReaderT (e, s) m a
--   }
--
-- evalPrecondition :: Precondition e s m a -> e -> s -> m a
-- evalPrecondition (Precondition r) e s = runReaderT r (e, s)


newtype Action e s m p = Action {
    runAction :: RWST e () s m p
  } deriving (
    Functor
  , Monad
  , MonadReader e
  , MonadState s
  , MonadTrans
  , MonadIO
  , MonadThrow
  )

evalAction :: Monad m => Action e s m a -> e -> s -> m a
evalAction m e s = return . fst =<< evalRWST (runAction m) e s

instance Show (Transition e s m p) where
  show = name

-- | Constructor for 'Transition'
--   Create unconditional 'Transition' which does nothing
mkTransition :: (Monad m) => String -> Transition e s m Property
mkTransition name' = MkTransition name' always sameState

-- | Define condition to 'Transition'
goif :: Transition e s m p -> (s -> Bool) -> Transition e s m p
goif t preCond' = t { preCond = preCond' }

-- | Define transition logic
goto :: Transition e s m p -> Action e s m p -> Transition e s m p
goto t transition' = t { transition = transition' }

-- | Do not change the state or eval any monadic actions
sameState :: Monad m => Action e s m Property
sameState = return (property True)

-- | Make 'Transition' unconditional
always :: s -> Bool
always = const True



-- listOfTransitions :: Testable p => Gen (Transition e s m) -> Gen [Transition e s m]
-- listOfTransitions g = sized $ \n ->
--   do k <- choose (0,n)
--   take k gen


--fl g =

-- | Generate and execute a list of 'Transition's
--   given environment 'env' and initial state 'state'
--   For longer running 'Transition's limit the list produced by 'g'
runFSM :: (Show s, Monad m, MonadCatch m, Testable p) => e -> s -> Gen (Transition e s m p) -> PropertyM m ()
--runFSM :: (Monad m, MonadCatch m, Testable p) => e -> s -> Gen (Transition e s m p) -> PropertyM m ()
runFSM env state g = do
  n <- pick arbitrary
  let m = replicateM_ n go
  return . fst =<< evalRWST m env state
  where
    go = do
      s <- get
      t <- lift . pick $ g `suchThat` flip preCond s
      lift $ handleError t s -- add transition chain to QuickCheck error in case of failure
      (liftProp . runAction . transition $ t) `catchTran` handleException -- run transition with additional handling
--      lift $ checkResult p

--    handleException :: Monad m => SomeException -> RWST e s m p
    handleException (e :: SomeException) = fail $ "Exception thrown: " <> show e

    liftProp = mapRWST run

-- -- | Similar to 'runFSM' but can be used with 'ContT' monad
-- --   'ContT' does not define 'MonadCatch' instance, so it it cannot be passed to 'runFSM'
-- runFSMCont :: (Show s, Monad m, MonadCatch m) => e -> s -> Gen [Transition e s (ContT Property m)] -> PropertyM (ContT Property m) ()
-- runFSMCont env state g = forAllM g $ \ts ->
--   let m = sequence_ . fmap toTransition $ ts
--   in evalAction m env (state, "")
--   where
--    toTransition t = do
--      (s, _) <- get
--      lift . pre $ preCond t s -- discard the transition if preCond t s == False
--      lift $ handleError t s -- add transition chain to QuickCheck error in case of failure
--      modify $ \(s', ss') -> (s', ss' <> formatState t s)
--      let m = Action . RWST $ \r (s', ss') -> do
--            (a'', s'', w'') <- runRWST (runAction (transition t)) r s'
--            return (a'', (s'', ss'), w'')
--      m `catchTranCont` handleException
--
--    handleException :: SomeException -> TransitionAction r (s, String) (ContT Property m)
--    handleException e = do
--      (_, ss) <- get
--      fail $ ss <> "Exception thrown: " <> show e


handleError :: (Show a, Monad m) => Transition e s m p -> a -> PropertyM m ()
handleError t s = monitor (mapTotalResult (addFailureReason t s))

addFailureReason :: Show a => Transition e s m p -> a -> Result -> Result
addFailureReason t s = \case
 r@MkResult{ ok = Just False } -> r { reason = formatState t s <> reason r}
 r -> r

formatState :: Show a => Transition e s m p -> a -> String
formatState t s = "\n(" <> show s <> ") -> " <> name t <> " -> "

-- checkResult :: Testable p => p -> PropertyM m ()
-- checkResult py = MkPropertyM $ \k -> do
--   pp <- unProperty . property $ py
--   MkRose res ts <- liftIO . reduceRose . unProp $ pp
--   case res of
--     MkResult { ok = Just True } -> k ()


-- | There is no MonadCatch instance for PropertyM so here is how it could be implemented
--catchTran :: (Exception e, MonadCatch m) => Action r s m p -> (e -> Action r s m p) -> Action r s m p
catchTran (RWST m) g = RWST $ \r s -> m r s `catchProp` \e -> runRWST (g e) r s

--catchProp :: (Exception e, MonadCatch m) => PropertyM m a -> (e -> PropertyM m a) -> PropertyM m a
catchProp (MkPropertyM f) g = MkPropertyM $ \h -> f h `catchGen` \e -> unPropertyM (g e) h

--catchGen :: (Exception e, MonadCatch m) => Gen (m a) -> (e -> Gen (m a)) -> Gen (m a)
catchGen (MkGen f) g = MkGen $ \q i -> f q i `catch` \e -> unGen (g e) q i


-- catchTranCont :: (Exception e, MonadCatch m) =>
--   Action r s (PropertyM (ContT Property m)) a ->
--   (e -> Action r s (PropertyM (ContT Property m)) a)
--   -> Action r s (PropertyM (ContT Property m)) a
-- catchTranCont (Action (RWST m)) g = Action . RWST $ \r s -> m r s `catchPropCont` \e -> (runRWST . runAction) (g e) r s
--
-- catchPropCont :: (Exception e, MonadCatch m) =>
--   PropertyM (ContT Property m) a -> (e -> PropertyM (ContT Property m) a) -> PropertyM (ContT Property m) a
-- catchPropCont (MkPropertyM f) g = MkPropertyM $ \h -> f h `catchGenCont` \e -> unPropertyM (g e) h
--
-- catchGenCont :: (Exception e, MonadCatch m) => Gen (ContT r m a) -> (e -> Gen (ContT r m r)) -> Gen (ContT r m a)
-- catchGenCont (MkGen f) g = MkGen $ \q i -> f q i `catchCont` \e -> unGen (g e) q i
--
-- catchCont :: (Exception e, MonadCatch m) => ContT r m a -> (e -> ContT r m r) -> ContT r m a
-- catchCont m g = mapContT (`catch` ((`runContT`return) . g)) m
