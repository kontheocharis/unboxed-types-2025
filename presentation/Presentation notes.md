---
title: Unboxed Dependent Types
date: 2025-06-13
authors: Constantine Theocharis and Ellis Kesterton
instutution: University of St Andrews
---

---

- Dependently-typed languages are great! By now there are implementations which are (close to) production-level readiness:
    - Idris
    - Agda
    - Lean
    - Coq
- All of them produce code which makes *excessive use of the heap*, and everything is boxed.
    - On the one hand, this is not as bad as it may seem---immutability enables lots of optimisations.
    - On the other hand, we cannot use these languages to (ergonomically) reason about unboxed data.

---

Why unboxed data?
- Contiguous arrays with constant-time indexing.
- Unboxed integers and packing small data.
- Protocol buffers (e.g. network packets)
- Memory mapped IO
- Data-driven design (e.g. entity-component systems)
If we want to do these things, we usually have to drop to a lower-level language such as C/C++/Rust, which means we lose the verification capabilities of dependent types.

---

Unboxed data would be a great fit for dependently-typed programming!
- Lots of indexing and slicing, perfect for some static bounds checks.
- Indexed-inductive views of low-level data structures.
- Towards verified low-level programming

---

Goals:
- A language where stack-allocated unboxed data is the default
- Explicit boxing primitive
- Efficient and safe indexing into data
- Support for dependently-sized data
- Zero-sized types = computational irrelevance
- Minimal other primitives: arrays are iterated sigma types
- 2LTT-compatible for metaprogramming

---

Non-goals:
- Manual memory management/no GC
- Holding references to stack values
- Lifetime analysis, uniqueness or linearity
- Unboxed closures

---

Order of operations

Layouts and types
Basic type formers


---

The core idea

Layouts describe arrangements of data in memory.

```hs
Layout : Set

0, 1, ptr, size : Layout

_+_ : Layout -> Layout -> Layout

_*_ : Nat -> Layout -> Layoyut
```

Types are indexed by their layout.

```hs
Ty : Layout -> Set

-- Grothendiek universe
Type : Ty 0
Tm (Type l) = Ty l
```

For compilation, we need a function `|_| : Layout -> Nat` for reserving space.

From now on, I will omit `Ty/Tm` and treat the metatheory as a 2LTT.

---

The standard type formers are now indexed by the appropriate layout:

- Functions are pointer-sized, and they box their closures.
```hs
A : Type a
B : A -> Type b
---------------
(x : A) '->' B x : Type ptr
```

- Pairs store their data contiguously
```hs
A : Type a
B : A -> Type b
---------------
(x : A, B x) : Type (a + b)
```

- The unit type exists for all layouts, and acts like padding
```hs
--------
() : Type u
```

- The universe of types is zero-sized, for all layouts
```hs
--------
Type l : Type 0
```

---

Then we have some non-standard type formers.

A boxing type which introduces a heap indirection, and is always pointer-sized:

```hs
A : Type a       
----------
Box A : Type ptr
```

We can go back and forth using `box` and `unbox` operators.

```hs
unbox : Box A ≈ A : box
```


---

Irrelevance

Naturally arises from the existence of zero-sized types.

It is in the form of a monadic modality 

```hs
0 : Type a -> Type 0

irr : A -> 0 A
already : 0 0 A -> 0 A
```

---

Which can be eliminated into zero-sized types.

```hs
P : 0 A -> Type 0
p : (x : A) -> P (irr x)
a : 0 A
------------------------
let irr x = a in p x : P a
```

With this we can construct a model of QTT with `{0, ω}`.

---
Runtime-sized data

A lot of the time we actually work with data whose size is only known at runtime!
Prototypical example: dynamic arrays.
Let's broaden our foundations a bit to account for this.

We reserve `Layout?` for *partially runtime-known layouts* defined as

```hs
_*_ : Nat -> Layout? -> Layout?
sta : Layout -> Layout?
```

where `Nat` is now partially static (we will use `NAT` for static), and has an evaluation function into `nat` in the object theory.

Only `Layout`'s size is known at compile-time, so there is no evaluation function `Layout? -> Layout` (besides, one is a presheaf over object-level contexts and the other isn't)

Now let's expand the universe of types:

```hs
Type? : Layout -> Ty 0
Type l = Type? (sta l)
```

Importantly, terms are still statically-sized: `Tm : Ty (sta b) -> Set`.

---

Generating runtime data

We introduce a new type former that represents the 'generation' of runtime-sized data

```hs
Make A : Type? l -> Type ptr
```

A `Make A` is thought of as `(size : nat, mk : *mut A -> ())`: some code to construct an `A` at some given location, knowing in advance that it takes up a certain amount of bytes.

For sized types `A : Type a`, we can go back and forth:

```hs
give : A ≃ Make A : emb
```

 
`⟦ give x ⟧ = (size = ⟦ |a| ⟧, mk = \x' => { *x' = ⟦ x ⟧; })`
`⟦ emb y ⟧ = let (_, mk) = ⟦ y ⟧ in mk ([0] * ⟦ |a| ⟧)`

---

Indexing

Now that we have unsized data, we need a way to be able to index into them to extract pieces.
Instead of iterated projections of data (which would take up intermediate stack space) we can build up and store indices that are 'instantly' able to access their target.

We introduce a new function-like type

```hs
A : Type? a
B : 0 A -> Type? b
------------------
(x : A) >> B x : Type size
```

`(x : A) >> B x` is an index into some `x : A` producing a `B x`. It is compiled as an integer offset.


When `A` is sized, we get an application operation

```hs
A : Type a
a : A
i : (x : A) >> B x
------------------
a[i] : Make (B a)
```

This is compiled as `⟦ a[i] ⟧ = *(&⟦ a ⟧ + ⟦ i ⟧)`

However, we do not have lambda abstractions. Instead, we have a 'section' composition operation

```hs
f : (x : A) >> B x
g : (x : 0 A) -> (y : B x) >> C y
-------------------------------
f . g : (x : A) >> C x[f]
```

Composition is simply addition of indices: `⟦ f . g ⟧ = ⟦ f ⟧ + ⟦ g ⟧`

and identities

```hs
this : A ~> A
```

`⟦ this ⟧ = 0`

This effectively results in dot record syntax

```hs
nth : Fin n -> List t >> t
players : Game >> List Player

game[players . nth 3]
```

---

We can now generalise boxing to unsized data:

```hs
Box : Type? l -> Type ptr
box : Make A -> Box A
```

- Boxing takes any 'recipe' `⟦ r ⟧ = (n, f)` to make `A` and effectively runs `x <- malloc(n); f(x)`.

We can recover the old `box`, in the case where `A : Type l`, with `give`.

---

How do we construct unboxed data?

Pairs and units generalise to the unsized setting: sized pairs are a special case.

```hs
() : Type u
------------
tt : Make ()

A : Type? a
B : 0 A -> Type? b
------------------------------------------------------
(_,_) : (x : Make A) -> Make (B x) -> Make (x : A, B x)
fst : (x : A, B x) >> A
snd : (p : (x : A, B x)) >> B p[fst]
```

`⟦ tt ⟧ = (|u|, \_ => ())`

`⟦ (a, b) ⟧ = (⟦ |a| ⟧ + ⟦ |b| ⟧, \(x, y) => { memcpy(x, ⟦ a ⟧); memcpy (y, ⟦ b ⟧) })`
`⟦ fst ⟧ = 0`
`⟦ snd ⟧ = ⟦ |a| ⟧`

However, functions don't.


---

Arrays

We can now reproduce arrays

```hs
Array : (T : Type t) -> (n : Nat) -> Type (n * l)
Array T 0 = () -- Type (0 * l) = Type 0
Array T (S n) = (t : T, Array T n) -- Type (S n * l) = Type (l + n * l)

replicate : (t : T) -> (n : Nat) -> Make (Array T n)
replicate t 0 = tt
replicate t (S n) = (give t, replicate t n)

get : Fin n -> Array T n >> T
get FZ = fst -- : (T, Array T n) >> T
get (FS i) = snd . get i -- : (T, Array T n) >> Array T n
```


---

Two-level type theory

A meta level can be added to the presented theory, making it a 2LTT. This means that we can write programs which are generic over layouts.

This is sort of what we have been doing so far..


---

Memory management

- So far I have ignored it.
- Reference counting can be implemented because we know where the pointers are (given an appropriate model of `Layout`).
- Alternatively, one could use a plug-and-play garbage collection such as Bohm GC.
- For now we are not looking explicit management because that would involve resource semantics and linear staging

---

Mutation

- I have ignored it too.
- Arguably quite important for performance when handling unboxed data.
- This can be done using either:
    - A 'primitive' ST monad 
    - A lens trick.

---


The mutation trick involves applying an update function to some data pointed to by an index.


```hs
update : Box A -> A >> B -> (B -> B) -> Box A

-- syntax:   update x p f   =   *x[p] = f
```


In a system with reference counting, we can implement this function as follows:
1. If the reference count of `x` is 1, then perform the modification in place.
2. If the reference count is > 1, duplicate the object (not the reference) and apply the modification to that.


---


Future work

