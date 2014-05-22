module Automaton ( pure, state, hiddenState, run, step
                 , andThen, combine, loop, count, average
                 , branch, extendDown
                 ) where

{-| This library is for structuring reactive code. The key concepts come
directly from [Arrowized FRP][afrp]. It is not yet clear how
valuable this is, so it is a great domain for experimentation and iteration
to see if we can make it a really useful tool.

This library aims to be a simple and minimal API that will help you get
started with Arrowized FRP (AFRP), which can be very hard to understand
from just the academic papers. From there, let us know on [the mailing
list](https://groups.google.com/forum/#!forum/elm-discuss) if you wrote
a larger program with it or have ideas of how to extend the API.

 [afrp]: http://haskell.cs.yale.edu/wp-content/uploads/2011/02/workshop-02.pdf

# Create
@docs pure, state, hiddenState

# Evaluate
@docs run, step

# Combine
@docs andThen, combine, loop,  branch

# Common Automatons
@docs count, average
-}

import Basics (..)
import Signal (lift,foldp,Signal)
import List (..)
import Maybe (Just, Nothing)

data Automaton a b = Step (a -> (Automaton a b, b))

{-| Run an automaton on a given signal. The automaton steps forward whenever the
input signal updates.
-}
run : Automaton i o -> o -> Signal i -> Signal o
run auto base inputs =
  let step a (Step f, _) = f a
  in  lift (\(x,y) -> y) (foldp step (auto,base) inputs)

{-| Step an automaton forward once with a given input. -}
step : i -> Automaton i o -> (Automaton i o, o)
step a (Step f) = f a

{-| Compose two automatons, chaining them together. That will typically
look something like this:

```haskell
move   : Automaton Spaceship Spaceship
rotate : Automaton Spaceship Spaceship

step = move `andThen` rotate
```
-}
andThen : Automaton i inner -> Automaton inner o -> Automaton i o
andThen f g =
  Step (\a -> let (f', b) = step a f
                  (g', c) = step b g
              in  (andThen f' g', c))


{-| Combine two automatons that work on the same kind of input.
-}
branch : Automaton i o1 -> Automaton i o2 -> Automaton i (o1, o2)
branch f g =
  Step <| \a -> let (f', b) = step a f
                    (g', c) = step a g
                 in (branch f' g', (b, c))

{-| Add an extra input "channel" to be ignored and just sent on as output.
Useful as a building block for more complex automata.
-}
extendDown : Automaton i o -> Automaton (i, extra) (o, extra)
extendDown auto = 
  Step <| \(i, ex) -> let (f, o) = step i auto
                       in (extendDown f, (o, ex))

{-| Adds an extra input "channel" to be ignored and sent on as output. Similar
to extendDown, but adds the input before the regular one. 
-}
extendUp : Automaton i o -> Automaton (extra, i) (extra, o)
extendUp auto = 
  Step <| \(ex, i) -> let (f, o) = step i auto
                       in (extendUp f, (o, ex))

{-| Feed an automaton's output into it's own input. Maintains a state within the
loop, and updates that state after each run of the loop. Requires an initial
state. 
-}
loop : state -> Automaton (i,state) (o,state) -> Automaton i o
loop state auto =
    Step <| \input -> let (auto', (output,state')) = step (input,state) auto
                      in  (loop state' auto', output)

{-| Combine a list of automatons into a single automaton that produces a
list.
-}
combine : [Automaton i o] -> Automaton i [o]
combine autos =
  Step <| \a -> let (autos', bs) = unzip (map (step a) autos)
                in  (combine autos', bs)

{-| Create an automaton with no memory. It just applies the given function to
every input.
-}
pure : (a -> b) -> Automaton a b
pure f = Step (\x -> (pure f, f x))


{-| Create an automaton with state. Requires an initial state and a step
function to step the state forward. For example, an automaton that counted
how many steps it has taken would look like this:

```haskell
count = Automaton a Int
count = state 0 (\\_ c -> c+1)
```

It is a stateful automaton. The initial state is zero, and the step function
increments the state on every step.
-}
state : b -> (a -> b -> b) -> Automaton a b
state s f = Step (\x -> let s' = f x s
                        in  (state s' f, s'))

{-| Create an automaton with hidden state. Requires an initial state and a
step function to step the state forward and produce an output.
-}
hiddenState : s -> (i -> s -> (o,s)) -> Automaton i o
hiddenState s f = Step (\x -> let (s',out) = f x s
                              in  (hiddenState out f, s'))

{-| Count the number of steps taken. -}
count : Automaton a Int
count = state 0 (\_ c -> c + 1)

type Queue t = ([t],[t])
empty = ([],[])
enqueue x (en,de) = (x::en, de)
dequeue q = case q of
              ([],[]) -> Nothing
              (en,[]) -> dequeue ([], reverse en)
              (en,hd::tl) -> Just (hd, (en,tl))
{-| Computes the running average of the last `n` inputs. -}
average : Int -> Automaton Float Float
average k =
  let step n (ns,len,sum) =
          if len == k then stepFull n (ns,len,sum)
                      else ((sum+n) / (toFloat len+1), (enqueue n ns, len+1, sum+n))
      stepFull n (ns,len,sum) =
          case dequeue ns of
            Nothing -> (0, (ns,len,sum))
            Just (m,ns') -> let sum' = sum + n - m
                            in ((sum' / toFloat len), (enqueue n ns', len, sum'))
  in  hiddenState (empty,0,0) step


{-- TODO(evancz): See the following papers for ideas on how to make this
library faster and better:

- Functional Reactive Programming, Continued
- Causal commutative arrows and their optimization

Speeding things up is a really low priority. Language features and
libraries with nice APIs and are way more important!
--}
