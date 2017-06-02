# Unboxed Union Types

<sub>Submitted: Fri 2nd June 2017, Updated: Fri 2nd June 2017</sub>

---

A union type is something which can be realised as one of many (usually two) types. `Either` is an example in scala -
`Either[A, B]` can be `Left[A]` or `Right[B]` - a value of either type can be used in a place where we ask for an `Either[A, B]`.

However, this is boxed so it's a bit clunky to use. Ideally we want to be able to drop an `A` or a `B` directly into
the space occupied by `Either[A, B]` without having to wrap it in `Left`/`Right` first. It's clunky enough doing this
once but if you had nested `Either`s it would get tedious very quickly.

Miles Sabin came up with a [great way](https://milessabin.com/blog/2011/06/09/scala-union-types-curry-howard) to represent unboxed union types in scala, a long time ago now.

His final example is:

```scala
def size[T: (Int |∨| String)#λ](t: T) =
  t match {
    case i: Int => i
    case s: String => s.length
  }
```

One thing I will repeat here from the blog post is the unfortunate state of escaping the union context. When you have a value `t: T`
which is understood by the compiler to be `Int or String`, how do you actually get the `Int` or the `String` out?

The easiest way is to pattern match like in the example given:

```scala
t match {
  case i: Int => doSomething(i)
  case s: String => doSomethingElse(s)
}
```

This is equivalent to what we might do with an `Either[Int, String]`:

```scala
t: Either[Int, String] match {
  case Left(i) => doSomething(i)
  case Right(s) => doSomethingElse(s)
}
```

But unfortunately due to erasure in the first example we lose the compiler's ability to check
the pattern match. If we forget a case, our code will just fail. If we add a case which cannot be reached, the compiler
will not warn us about it. We will not be solving this problem (yet) - I am just pointing it out as a drawback to unboxed
union types in scala.

# Arbitrary Arity

One downfall with the approach in Miles' blog post is the fact you're stuck with just two values in the
union. What if we wanted `A` or `B` or `C`? What if we wanted an arbitrarily wide union type? How would you achieve that
without defining `Union3` and `Union4`, etc?

First of all, we must be aware of additional concerns with nested unions that do not exist when dealing with unions
of only two types:

- `Union[A, B]` should be able to be used in place of a `Union[A, B, C]` (if `T` is `A` or `B` it is certainly `A` or `B` or `C`!)
- `Union[A, A, B]` should be able to be used in place of a `Union[A, B]`

Our first attempt looked a lot like Miles' approach, just nested. So one might end up with something that
looked a little like this:

`Union[Union[Union[G, H], K], Union[B, C]]`

which would be read as 'G or H or K or B or C'.

But that was very noisy, and bug-ridden. The implicits required to generate it were constructive:

- Commutativity: `Union[A, B] => Union[B, A]`
- Associativity: `Union[A, Union[B, C]] => Union[Union[A, B], C]`
- Point: `A => Union[A, T]` for any `T`

Because these are constructive there are a lot of different ways of combining them to prove the following two
types are the 'same':

`Union[Union[Union[G, H], K], Union[Union[H, U], C]]`

`Union[Union[Union[Union[C, G], H], K], U]`

This led to a lot of diverging implicit expansion compile-time errors in unexpected places. It just wasn't working, so we adjusted our thinking.

All those repeated 'unions' and brackets are just fluff; implementation details. What we actually want to do is represent
the union types as a Set of types: we have this collection of types and we're ignoring duplicates and the order does not matter.

A true set of types is difficult, since in any implementation (afaik!) there will be a natural order of types imposed by the compiler.
But a list is easy, it's just an `HList`. As long as our type classes and code around our `HList` implementation ignore repetitions
and order, it should represent precisely what we want to represent.

# HList approach

So here's a basic `Union` implementation, built exactly the same way as an `HList` (but just type-level only, no values allowed)

```scala
// Analagous to HList
sealed trait Union

// Analagous to HCons and ::
trait :|:[+H, +T <: Union] extends Union

// Analagous to HNil
sealed trait UNil extends Union
```

A union type would end up looking like this: `Int :|: String :|: Boolean :|: UNil` - easily extendable to an arbitrary
number of types.

Now we just have to be able to use and interpret it.
The first thing we did was decide on what we wanted our user-interface to be.
We chose the following type class:

```scala
trait OneOf[T, U <: Union]
```

which represents evidence that `T` satisfies the union `U` (that is, `T` is one `U`'s constituent types).
If we have one of these objects in scope we can proceed and we know that our eventual pattern match will be safe
even if the compiler sadly doesn't.

A function that uses it might look like this:

```scala
def foo[T](union: T)(implicit unionEv: OneOf[T, Int :|: String :|: UNil]): String = union match {
  case i: Int => i.toString
  case s: String => s
}
```

Our implicit functions generating `OneOf` instances would only let such a `OneOf` be generated in the case of `T` being `Int` or `String`.
So what are these implicits?

We need some utilities first.

## MemberOf

First, a way of telling if a type `T` is a member of a union `U`. We do this with the following type class:

```scala
trait MemberOf[T, U <: Union]
```

If we have an implicit in scope with this type, we understand it to mean 'T is a member of U'

We generate these implicit values below:

```scala
sealed trait MemberOf[T, U <: Union]

object MemberOf {

  // If H is the first type in an Union U, we trivially know that H is in U
  implicit def baseCase[H, U <: Union]: MemberOf[H, H :|: U] = null

  // If T is in the union U, we know T is in the Union H:|:U for any H
  implicit def recursiveCase[H, U <: Union, T](implicit member: T MemberOf U): T MemberOf (H :|: U) = null

}
```

This covers all cases for `MemberOf`.

## SubUnionOf

Our next utlity type class is a way of proving that a certain `Union` is a subunion of another - that is, every
constituent type of the first appears in the second. We do this with the following trait:

```scala
trait SubUnionOf[U <: Union, T <: Union]
```

If we have an implicit object in scope with type `SubUnionOf[A, B]` it acts as proof that every member of `A` is
also a member of `B`, and that we can freely use an `A` union in place of a `B` union.
We generate these implicit values as below:

```scala
object SubUnionOf {

  // If U1 is a member of U, then U1 :|: UNil is most definitely a subunion of U
  implicit def fromMemberCase[U1, U <: Union](implicit s: U1 MemberOf U): SubUnionOf[U1 :|: UNil, U] = null

  // If T1 is a member of U, and T is a subunion of U, then T1 :|: T is a subunion of U
  implicit def recursiveCase[U <: Union, T1, T <: Union](
    implicit mem: T1 MemberOf U,
    sub: T SubUnionOf U
  ): (T1 :|: T) SubUnionOf U = null

}
```

It's a little bit more complicated but if you ignore the syntax bloat and read it as logical implication, as in my
comments, it's not too bad.

Note that we have `(A :|: A :|: UNil) SubUnionOf (A :|: UNil)` available for any `A`, thanks to our `MemberOf` type class. This takes
care of our 'repeated type' requirement. Also note that because we ask for each type's membership proof individually, the order does
not matter either. We have `(A :|: B :|: UNil) SubUnionOf (B :|: A :|: UNil)` for any types `A` and `B`.

## OneOf

Finally, we have enough to construct our `OneOf` implicit functions.

There are two cases we need to construct a `OneOf` for:

- The case where we're using a type we know about (simple `MemberOf` checking).
- The case where we're trying to use a union type in place of another union type (`SubUnion` checking).

```scala
trait OneOf[T, U <: Union]

object OneOf {

  // If T is a member of the union U then we know T is 'one of' U, by our definition of what 'OneOf' means
  implicit def fromMemberProof[U <: Union, T](implicit s: T MemberOf U): T OneOf U = null

  // If we have evidence OneOf[T, Ev] it means T is a member of Ev, and if we know Ev
  // is a subunion of Target, then we can deduce T is also one of Target
  implicit def nestedOneOfProof[T, Ev <: Union, Target <: Union](
    implicit ev: T OneOf Ev,
    sub: Ev SubUnionOf Target
  ): T OneOf Target = null

}
```

In words, if we have an existing `OneOf[T, U]` for a certain generic type `T` and some
union `U`, we can repurpose it into another `OneOf[T, X]` if we can squeeze `U` into `X` via our utility type classes.

## Syntax

One last thing is the syntax for use. It's a bit annoying to have a `OneOf` implicit parameter explicitly passed around,
we'd ideally like it more obvious that our generic `T` is constrained to be a union type.

Thankfully we can do the same trick Miles Sabin does in his blog post, and have a type alias:

```scala
// Note in reality you can't do this, you'd have to rename the existing `OneOf` trait
// In our project we've called it 'OneOfType'
type OneOf[H <: Union] = { type l[T] = OneOf[T, H] }
```

Now instead of writing

```scala
def foo[T](t: T)(implicit unionEv: OneOf[T, Int :|: String :|: Boolean :|: UNil]): Any = ???
```

we can write

```scala
def foo[T: OneOf[Int :|: String :|: Boolean :|: UNil]#l](t: T): Any = ???
```

which makes it a bit nicer to read and explain what's going on with `T`. It's a shame about the lambda `l` hanging around,
but it is what it is.

## Final code

Our final code looks like this:

```scala
object Testing {
  def foo[T: OneOf[Int :|: String :|: Boolean :|: UNil]#l](t: T): String = t match {
    case s: String => s
    case b: Boolean => b.toString
    case i: Int => i.toString
  }

  foo("hello") // compiles
  foo(5)       // compiles
  foo(true)    // compiles
  foo('c')     // does not compile

  // We can nest them, too:
  def bar[T: OneOf[String :|: Int :|: UNil]#l](t: T) = foo(t)  // Compiles

  // But we can't mis-match them - Char is not a member of foo's union
  // so this will not compile
  def baz[T: OneOf[String :|: Char :|: UNil]#l](t: T) = foo(t)
}
```

It all works as expected!

## Restriction

Note that because we're working with an unboxed union type, we can't use it as a real type. We can't have a `List`
of our union types, or have a function return one. They exist purely as flags in the compiler, interpreted by us
in our implicit methods generating our utility type classes.
