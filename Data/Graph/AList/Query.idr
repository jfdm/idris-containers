||| Example Queries over AList implemented graphs.
|||
||| TODO make query higher-order.
module Data.Graph.AList.Query

import Effects
import Effect.State
import Effect.StdIO

import Data.Graph.AList.Implementation

import Data.Queue
import Data.Stack

%access public

-- --------------------------------------------------------------------- [ BFS ]
||| The effects used in a BFS.
BfsEffs : List EFFECT
BfsEffs = [ 'next ::: STATE (Queue Node),
            'seen ::: STATE (List Node),
            STDIO]

||| Traverse the given graph using a BFS, printing the visited nodes
||| in order of visit.
private
doTraceBFS : (Ord n, Show n) => Graph n e -> {BfsEffs} Eff ()
doTraceBFS g = do
   q <- 'next :- get
   if isQEmpty q
     then pure () -- Stop if all nodes have been traversed.
     else do
       let (curr, q') = popQ q
       'next :- put q'
       -- Do the thing we do at the nodes.
       putStrLn $ show curr

       -- Move on
       let es = getSuccs curr g
       mapE doMove $ fromMaybe Nil es

       -- Repeat
       doTraceBFS g
  where
    doMove : Node -> {BfsEffs} Eff ()
    doMove n = do
      visited <- 'seen :- get
      case elem n visited of
        True => pure ()
        False => do
          'seen :- update (\xs => [n] ++ xs)
          'next :- update (\xs => pushQ n xs)

||| Traverse the given graph using a BFS, printing the visited nodes
||| in order of visit.
traceBfsIO : (Ord v, Show v) => Node -> Graph v e -> IO ()
traceBfsIO n g = runInit ['next := initQ n, 'seen := Nil, ()] $ doTraceBFS g

-- --------------------------------------------------------------------- [ DFS ]
||| The Effects used in a DFS.
DfsEffs : List EFFECT
DfsEffs = [ 'next ::: STATE (Stack Node),
            'seen ::: STATE (List Node),
            STDIO]

||| Traverse the given graph using a DFS, printing the visited nodes
||| in order of visit.
doTraceDFS : (Ord n, Show n) => Graph n e -> {DfsEffs} Eff ()
doTraceDFS g = do
    s <- 'next :- get
    if isSEmpty s
    then pure ()
    else do
      let (curr, s') = popS s
      'next :- put s'
      visited <- 'seen :- get
      if elem curr visited
        then pure ()
        else do
          putStrLn $ show curr
          let es = getSuccs curr g
          'seen :- update (\xs => [curr] ++ xs)
          'next :- update (\xs => pushSThings (fromMaybe Nil es) s)
      doTraceDFS g

||| Traverse the given graph using a DFS, printing the visited nodes
||| in order of visit.
traceDfsIO : (Ord v, Show v) => Node -> Graph v e -> IO ()
traceDfsIO n g = runInit ['next := initS n, 'seen := Nil, ()] $ doTraceDFS g
-- --------------------------------------------------------------------- [ EOF ]
