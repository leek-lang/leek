# Leek

![GitHub](https://img.shields.io/github/license/leek-lang/leek?color=blue)
[![Build Status](https://img.shields.io/endpoint.svg?url=https%3A%2F%2Factions-badge.atrox.dev%2Fleek-lang%2Fleek%2Fbadge%3Fref%3Dmaster&style=flat)](https://actions-badge.atrox.dev/leek-lang/leek/goto?ref=master)

<p align="center">
    <img src="https://user-images.githubusercontent.com/49880655/234137537-847f2b36-6aad-43d8-9c74-69c5b7231d3d.svg" width="250">
</p>


In modern times, there are many strategies for managing memory such as reference counting, garbage collection, RAII, and of course manual memory management.
However, with many gigabytes of RAM now an established standard in new systems, why bother worrying about memory at all?

Leek uses a bleeding edge and _blazingly fast_ memory management strategy called "exiting".
Memory is allocated as needed and avoids slow de-allocation calls by not doing them.
Your operating system is more than capable of freeing the used memory when your program exits, so why bother incurring wasteful runtime cost?

Leek enables you to move fast and run away from your problems. Even if you manage to use up all of the available system memory, modern operating systems have sophisticated swap file implementations. This allows you to use disk space as RAM when there is no physical memory left.

## Edge Ready

Modern serverices and applications don't keep a persistent server running. Thats old school! Now, serverless edge functions are dominating the industry with low deployment costs and automatic scaling.

Leek's memory management ideology aligns very well with the edge computing model. Leek starts fast and doesn't worry about deallocating memory since the instance will only live for a very short period of time. This makes Leek a great choice for your next serverless edge application (once an HTTP package is implemented).

## Examples

Leek uses a Rust inspired syntax, but differs slightly. Semicolons are not necessary anywhere, and commas are not necessary in many places either.

### 1. Hello World

All binary programs require a `main` function. To print to the standard output, use the built in global `println` function.

```leek
fn main() {
    println("Hello, world!")
}
```

### 2. Local Variables

In Leek, allocating variables on the stack violates the principle of memory management through exiting. Thats why, all local variables get allocated on the heap. Declare a variable with the `leak` keyword like so:

```leek
fn main() {
    leak a = 0

    // Prints "0"
    println("{}", a)

    a = 1

    // Prints "1"
    println("{}", a)
}
```

### 3. Functions

Arguments to functions can be defined with the comma separated `<identifier>: <type>` syntax, and return types can be declared using an arrow (`->`).
To return a value from a function, use the `yeet` keyword.

```leek
fn add(a: i32, b: i32) -> i32 {
    yeet a + b
}

fn main() {
    // Prints "3"
    println("{}", add(1, 2))
}
```

### 4. Constant Variables

Declare constants with the `perm` keyword. A strict type definition is required. Constant variables will not leak any memory at runtime, but can not be mutated.

```leek
perm PI: f64 = 3.141592653589793

fn main() {
    // Prints "3.141592653589793"
    println("{}", PI)
}
```

### 5. Static Variables

Declare static variables with the `hold` keyword. A strict type definition is required. Static variables will be lazily allocated at runtime, and can be mutated at any point in the program.

```leek
hold NUM: i32 = 0

fn mutate() {
    NUM += 1
}

fn main() {
    // Prints "0"
    println("{}", NUM)

    mutate()

    // Prints "1"
    println("{}", NUM)

    mutate()

    // Prints "2"
    println("{}", NUM)
}
```

### 6. Structs

Define structs with the `struct` keyword, and declare fields with their name and type (no commas required!). Create a struct with the name and its members inside brackets. Access its fields with dot notation.

```leek
struct Person {
    name: String
    age: i32
}

fn main() {
    leak alice = Person {
        name: "Alice"
        age: 18
    }

    // Prints "Alice is 18 years old."
    println("{} is {} year old.", alice.name, alice.age)
}
```

### 7. Struct Methods

Leek does not support object oriented programming, but functions can be scoped to a struct and accessed with dot notation in a similar way to many OOP style languages. This is syntactic sugar for passing in the struct as the first argument to a function.

```leek
struct Person {
    first_name: String
    last_name: String
}

fn Person::full_name(this) -> String {
    yeet format("{} {}", this.first_name, this.last_name)
}

fn main() {
    leak root = Person {
        first_name: "John"
        last_name: "Smith"
    }

    println("{}", root.full_name())
}
```
