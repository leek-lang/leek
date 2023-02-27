# Leek

In modern times, there are many strategies for managing memory such as reference counting, garbage collection, RAII, and of course manual memory management.
However, with many gigabytes of RAM now an established standard in new systems, why bother worrying about memory at all?

Leek uses a bleeding edge and _blazingly fast_ memory management strategy called "exiting".
Memory is allocated as needed and avoids slow de-allocation calls by not doing them.
Your operating system is more than capable of freeing the used memory when your program exits, so why bother incurring wasteful runtime cost?

Leek enables you to move fast and run away from your problems. Even if you manage to use up all of the available system memory, modern operating systems have sophisticated swap file implementations. This allows you to use disk space as RAM when there is no physical memory left.

## Examples

Leek uses a Rust inspired syntax, but differs slightly. Semicolons are not necessary anywhere, and commas are not necessary in many places either.

### Hello World

All binary programs require a `main` function. To print to the standard output, use the built in global `println` function.

```leek
fn main() {
    println("Hello, world!")
}
```

### Local Variables

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

### Functions

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

### Constant Variables

Declare constants with the `perm` keyword. A strict type definition is required. Constant variables will not leak any memory at runtime, but can not be mutated.

```leek
perm PI: f64 = 3.141592653589793

fn main() {
    // Prints "3.141592653589793"
    println("{}", PI)
}
```

### Static Variables

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

### Structs

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
