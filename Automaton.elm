module Automaton
    ( Automaton, pure, state, hiddenState
    , run, step
    , (>>>), (<<<)
    , branch, pair, merge
    , first, second
    , combine, loop
    , count, average
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
@docs (>>>), (<<<), branch, pair, merge, first, second, combine, loop

# Common Automatons
@docs count, average
-}

import Basics (..)
import Signal ( lift, foldp, Signal )
import List (..)

data Automaton a b =
    Step (a -> (Automaton a b, b))

{-| Run an automaton on a given signal. The automaton steps forward whenever the
input signal updates.

      count : Automaton a Int

      run count Mouse.clicks
-}
run : Automaton i o -> o -> Signal i -> Signal o
run auto base inputs =
  let step a (Step f, _) = f a
  in
      lift (\(x,y) -> y) (foldp step (auto,base) inputs)

{-| Step an automaton forward once with a given input.

Say we start with the `count` automaton, which begins with the counter at zero.
When we run `step 42 count` we get back a new automaton with the counter at
1 and the value 1. The original `count` automaton is unchanged, so we need to
use the new automaton to use the latest state.
-}
step : i -> Automaton i o -> (Automaton i o, o)
step a (Step f) = f a

{-| Compose two automatons into a pipeline. For example, lets say we have a way
to gather wood from the trees and a way to build a ship out of wood.

      gatherWood : Automaton Trees Wood
      buildShip  : Automaton Wood  Ship

      createShip : Automaton Trees Ship
      createShip = gatherWood >>> buildShip
-}
(>>>) : Automaton i inner -> Automaton inner o -> Automaton i o
(>>>) f g =
  Step <| \a ->
    let (f', b) = step a f
        (g', c) = step b g
    in
        (f' >>> g', c)

{-| Compose two automatons into a pipeline. For example, lets say we have a way
to gather wood from the trees and a way to build a ship out of wood.

      gatherWood : Automaton Trees Wood
      buildShip  : Automaton Wood  Ship

      createShip : Automaton Trees Ship
      createShip = buildShip <<< gatherWood
-}
(<<<) : Automaton inner o -> Automaton i inner -> Automaton i o
(<<<) g f =
  Step <| \a ->
    let (f', b) = step a f
        (g', c) = step b g
    in
        (g' <<< f', c)

{-| Take a single input and branch it out into two different results.

      buildShip  : Automaton Wood Ship
      buildHouse : Automaton Wood House

      build : Automaton Wood (Ship,House)
      build = branch buildShip buildHouse
-}
branch : Automaton i o1 -> Automaton i o2 -> Automaton i (o1, o2)
branch f g =
  Step <| \a ->
    let (f', b) = step a f
        (g', c) = step a g
    in
        (branch f' g', (b, c))

{-| Combine two independent automatons. The new automaton takes a pair of
inputs and produces a pair of outputs. In this case we convert two separate
values into two separate piles of wood:

      tsunami : Automaton Ship  Wood
      tornado : Automaton House Wood

      disaster : Automaton (Ship,House) (Wood,Wood)
      disaster = pair tsunami tornado
-}
pair : Automaton i1 o1 -> Automaton i2 o2 -> Automaton (i1, i2) (o1, o2)
pair f g = 
  Step <| \(a, b) ->
    let (f', c) = step a f
        (g', d) = step b g
    in
        (pair f' g', (c, d))

{-| Create an automaton that takes in a tuple and returns a tuple, but only
transform the *first* thing in the tuple.

      build       : Automaton Wood (Ship,House)
      upgradeShip : Automaton Ship Yacht

      buildNicer : Automaton Wood (Yacht,House)
      buildNicer = build >>> first upgradeShip

It may be helpful to know about the following equivalence:

      first upgradeShip == pair upgradeShip (pure id)
-}
first : Automaton i o -> Automaton (i, extra) (o, extra)
first auto = 
  Step <| \(i, ex) ->
    let (f, o) = step i auto
    in
        (first f, (o, ex))

{-| Create an automaton that takes in a tuple and returns a tuple, but only
transform the *second* thing in the tuple.

      build        : Automaton Wood (Ship,House)
      upgradeHouse : Automaton House Palace

      buildNicer : Automaton Wood (Ship,Palace)
      buildNicer = build >>> second upgradeHouse

It may be helpful to know about the following equivalence:

      second upgradeHouse == pair (pure id) upgradeHouse
-}
second : Automaton i o -> Automaton (extra, i) (extra, o)
second auto = 
  Step <| \(ex, i) ->
    let (f, o) = step i auto
    in
        (second f, (ex, o))

{-| Create an automaton that takes a branched input and merges it into a single
output.

      disaster : Automaton (Ship,House) (Wood,Wood)
      pileWood : Wood -> Wood -> Wood

      disasterRelief : Automaton (Ship,House) Wood
      disasterRelief = disaster >>> merge pileWood

It may be helpful to notice that merge is just a variation of `pure`:

      merge plieWood == pure (\(logs,sticks) -> pileWood logs sticks)
-}
merge : (i1 -> i2 -> o) -> Automaton (i1,i2) o
merge f = pure (uncurry f)

{-| Turn an automaton into a loop, feeding some of its output back into itself!
This is how you make a stateful automaton the hard way.

      data Feelings = Happy | Sad

      stepPerson : (Action, Feelings) -> (Reaction, Feelings)

      person : Automaton Action Reaction
      person = loop Happy (pure stepPerson)

This example is equivalent to using `hiddenState` to create a `person`, but the
benefit of loop is that you can add state to *any* automaton. We used
`(pure stepPerson)` in our example, but something more complex such as
`(branch f g >>> merge h)` would work just as well with `loop`.
-}
loop : state -> Automaton (i,state) (o,state) -> Automaton i o
loop state auto =
  Step <| \input ->
    let (auto', (output,state')) = step (input,state) auto
    in 
        (loop state' auto', output)

{-| Combine a list of automatons into a single automaton that produces a
list.
-}
combine : [Automaton i o] -> Automaton i [o]
combine autos =
  Step <| \a ->
    let (autos', bs) = unzip (map (step a) autos)
    in
        (combine autos', bs)

{-| Create an automaton with no memory. It just applies the given function to
every input.

      burnCoal : Coal -> Energy

      powerPlant : Automaton Coal Energy
      powerPlant = pure burnCoal

The term *pure* refers to the fact that [the same input will always result in
the same output](http://en.wikipedia.org/wiki/Pure_function).
-}
pure : (a -> b) -> Automaton a b
pure f = Step (\x -> (pure f, f x))


{-| Create an automaton with state. Requires an initial state and a step
function to step the state forward. For example, an automaton that counted
how many steps it has taken would look like this:

      count = Automaton a Int
      count = state 0 (\_ c -> c+1)

It is a stateful automaton. The initial state is zero, and the step function
increments the state on every step.
-}
state : b -> (a -> b -> b) -> Automaton a b
state s f =
  Step <| \x ->
    let s' = f x s
    in
        (state s' f, s')

{-| Create an automaton with hidden state. Requires an initial state and a
step function to step the state forward and produce an output.

      data Feelings = Happy | Sad

      stepPerson : Action -> Feelings -> (Reaction, Feelings)

      person : Automaton Action Reaction
      person = hiddenState Happy stepPerson

Notice that a `person` has feelings, but like [the
Behaviorists](http://en.wikipedia.org/wiki/Behaviorism), we do not need to
worry about that as an outside observer.
-}
hiddenState : s -> (i -> s -> (o,s)) -> Automaton i o
hiddenState s f =
  Step <| \x ->
    let (s',out) = f x s
    in
        (hiddenState out f, s')

{-| Count the number of steps taken. -}
count : Automaton a Int
count = state 0 (\_ c -> c + 1)

type Queue t = ([t],[t])

empty = ([],[])

enqueue x (en,de) = (x::en, de)

dequeue q =
  case q of
    ([],[]) -> Nothing
    (en,[]) -> dequeue ([], reverse en)
    (en,hd::tl) -> Just (hd, (en,tl))

{-| Computes the running average of the last `n` inputs. -}
average : Int -> Automaton Float Float
average k =
  let step n (ns, len, sum) =
          if len == k
            then stepFull n (ns,len,sum)
            else ((sum+n) / (toFloat len+1), (enqueue n ns, len+1, sum+n))

      stepFull n (ns,len,sum) =
          case dequeue ns of
            Nothing -> (0, (ns,len,sum))
            Just (m,ns') ->
              let sum' = sum + n - m
              in  ((sum' / toFloat len), (enqueue n ns', len, sum'))
  in
      hiddenState (empty,0,0) step


{-- TODO(evancz): See the following papers for ideas on how to make this
library faster and better:

- Functional Reactive Programming, Continued
- Causal commutative arrows and their optimization

Speeding things up is a really low priority. Language features and
libraries with nice APIs and are way more important!
--}
