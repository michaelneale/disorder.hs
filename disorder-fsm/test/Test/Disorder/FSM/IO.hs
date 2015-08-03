{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Disorder.FSM.IO where

import           Data.IORef
import           Data.Monoid
import           Control.Applicative hiding (empty)
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class

import           Disorder.FSM
--import           Disorder.Core.Property

import           Test.QuickCheck
import           Test.QuickCheck.Monadic


-- | "External" stateful system "Mutable stack" which is tested here
newtype Stack a = Stack {
    _toRef :: IORef [a]
  }

empty :: IO (Stack a)
empty = Stack <$> newIORef []

push :: Stack a -> a -> IO ()
push (Stack r) a = modifyIORef r (a:)

pop :: Stack a -> IO a
pop (Stack r) = readIORef r >>= \case
  [] -> fail "Empty stack"
  (a:ls) -> do
    writeIORef r ls
    return a

top :: Stack a -> IO (Maybe a)
top (Stack r) = readIORef r >>= \case
  [] -> return Nothing
  ls -> return $ Just (head ls)

size :: Stack a -> IO Int
size (Stack r) = readIORef r >>= return . length

-- | Environment here is the 'Stack' itself
type Environment a = Stack a

-- | Model state of the 'Stack' is just a list
type Model a = [a]

type StackTransition a = Transition (Environment a) (Model a) IO Property

-- | Pushes random element to stack
genPush :: Gen (StackTransition Int)
genPush = do
  a <- arbitrary
  return $ mkTransition ("push " ++ show a) `goto` do
    s <- ask
    liftIO $ push s a
    -- updates the model
    modify $ (a:)
    return $ True === True

-- | Broken 'push' which doesn't actually push negative elements
genInvalidPush :: Gen (StackTransition Int)
genInvalidPush = do
  a <- arbitrary
  return $ mkTransition ("invalid_push " ++ show a) `goto` do
    s <- ask
    -- | this is where it is brocken
    unless (a < 0) $ liftIO $ push s a
    -- | it does modify the model correctly (so it won't match the 'RealWorld')
    modify $ (a:)
    return $ True === True

-- | Pops an element from 'Stack'
genPop :: Gen (StackTransition Int)
genPop =
  return $ mkTransition "pop" `goif` (not . null) `goto` do
    s <- ask
    a <- liftIO $ pop s
    l <- get
--    lift $ assert (a == head l)
    -- updates the Model
    modify $ tail
    return $ a === head l

-- | Does not specify 'goif' pre-condition so the assertion can fail
--   when it is executed with empty 'Stack'
genInvalidPop :: Gen (StackTransition Int)
genInvalidPop =
  return $ mkTransition "invalid_pop" `goto` do
    s <- ask
    l <- get
    -- this may 'fail'
--    lift $ assert (not . null $ l)
    a <- liftIO $ pop s
    -- and this may 'fail' if the model is out of sync with 'RealWorld'
--    lift $ assert (a == head l)
    modify $ tail
    return $ property (l /= []) .&&. a === head l

-- | Does not specify 'goif' pre-condition so it may throw exception
genPopException :: Gen (StackTransition Int)
genPopException =
  return $ mkTransition "invalid_pop" `goto` do
    s <- ask
    l <- get
    -- will throw exception on empty 'Stack'
    a <- liftIO $ pop s
--    lift $ assert (a == head l)
    modify $ tail
    return $ a === head l

-- | Reads an element on 'Stack' top
genTop :: Gen (StackTransition Int)
genTop =
  return $ mkTransition "top" `goto` do
    s <- ask
    ma <- liftIO $ top s
    l <- get
    -- checks with model
    case (ma, l) of
      (Just a, (x:_)) -> return $ a === x
      (Nothing, _) -> return $ l === []
      inv -> fail $ "invalid state: " <> show inv

genSize :: Gen (StackTransition Int)
genSize =
  return $ mkTransition "size" `goto` do
    s <- ask
    ss <- liftIO $ size s
    l <- get
    return $ ss === length l

-- | Shall never fail since only correct transitions are used
prop_success :: Property
prop_success = monadicIO $ do
  s <- liftIO empty
  runFSM s [] . oneof $ [genPush, genPop, genTop, genSize]

-- | fails due to invalid 'pop'
prop_pop_assert_error :: Property
prop_pop_assert_error = expectFailure . monadicIO $ do
  s <- liftIO empty
  runFSM s [] . oneof $ [genPush, genInvalidPop, genTop, genSize]

-- | fails due to invalid 'push'
prop_push_assert_error :: Property
prop_push_assert_error = expectFailure . monadicIO $ do
  s <- liftIO empty
  runFSM s [] . oneof $ [genInvalidPush, genPush, genPop, genTop, genSize]

-- | Produces "invalid" transition less frequently
--   thus generating longer transition list
prop_assert_error_longer_chain :: Property
prop_assert_error_longer_chain = expectFailure . monadicIO $ do
  s <- liftIO empty
  runFSM s [] . frequency $ [
      (10, genPush)
    , (1, genInvalidPush)
    , (10, genTop)
    , (10, genPop)
    , (1, genInvalidPop)
    , (10, genSize)
    ]

-- | Fails due to exception with output identical to 'fail' failure
prop_state_exception :: Property
prop_state_exception =  expectFailure . monadicIO $ do
  s <- liftIO empty
  runFSM s [] . oneof $ [genPush, genPopException, genTop, genSize]


return []
tests :: IO Bool
tests = $quickCheckAll
