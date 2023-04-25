# Leek Compiler

<img width="3104" alt="Leek Compiler" src="https://user-images.githubusercontent.com/49880655/234275312-0e618682-0cab-4435-b15b-bb6ed57de6ba.png">

The Leek Bootstrap Compiler is written in Rust, and is divided into multiple modules. The entire compilation pipeline is described as follows:

## Frontend

The first step to compiling a Leek program is to pass through the frontend of the compiler.

### Character Reader

The Character Reader is a peekable iterator over the characters in an input source and provides a unified interface over multiple input types. The resulting stream of characters are passed to and consumed by the Lexer in the next step.

### Lexer

The Lexer builds up higher level tokens from the character stream, and creates another peekable iterator over these tokens. At this step, integer literals are classified, keywords are recognized, and operators are classified. The resulting peekable stream of tokens is passed to the Parser in the next step.

### Parser

The Parser consumes the tokens created by the Lexer and constructs a parse tree consisting of all of the input tokens organized into "Non-Terminals" (i.e. higher level pieces of syntax like functions, struct definitions, and variables). An important note is that at this stage, all of the input from the source file including whitespace (and not including redundant whitespace) is preserved and can be reconstructed into a source file for auto-formatting. This higher level parse tree is passed onto the AST Builder in the next step.

### AST Builder

The AST Builder is responsible for transforming the loose parse tree into a more well defined syntax tree. At this stage, individual semantics (such as formatting and whitespace) from the source file are lost, and the resulting AST (Abstract Syntax Tree) only contains the significant parts of the input program. Function, Struct, and Enum definitions are enumerated, and code blocks are organized into well defined statements. This AST is very versatile and can be used for many other forms of processing such as transformation. Errors in this step should be impossible if the Parser is made correctly, and we ensure this through the superfluous use of static asserts. This step is the last stage in the frontend of the compiler. After this, the AST is passed to the middle of the compiler to create a more verbose and more easily optimizable intermediary representation.

## Middle

The middle of the compiler is where a majority of the work is done. Here the program is type-checked and expanded to remove syntactic sugar. Optimizations are applied in several passes, and a low level representation is generated.

### HIR (High-Level Intermediary Representation)

The HIR, or High-Level Intermediate representation, is the form of the program that is nicer to work with for static analysis. Local variables are hoisted to the top of functions, and identifiers are checked for existence.

### Type Checking

At this stage, the HIR is traversed in order to assign types to variables and create another intermediary representation with much more useful type information. Struct fields and methods are checked to exist, and types of function arguments are validated. The resulting type checked program is called the MIR (Mid-Level Intermediary Representation).

### MIR (Mid-Level Intermediary Representation)

The MIR, or Mid-Level Intermediate representation, is the final form that the program takes before it can be optimized and thoroughly analyzed. It contains all of the rich type information necessary to be able to optimize our program, remove dead code references, and perform static analysis.

### Optimization

Once the MIR is generated, many steps can be taken to optimize the program. Loops can be unrolled to prevent branching, functions can be inlined, and constant expressions can be recursively evaluated.

### LIR (Low-Level Intermediary Representation)

After lowering down to MIR, we are almost ready to generate assembly. The last step before passing our program to the backend is to lower one step further to LIR, or Low-Level Intermediary Representation. LIR is a hardware-based representation that corresponds to an abstract target architecture with an infinite number of registers. This is useful because it allows for more optimizations that could not have been achieved in MIR. Conditional branches are fully expanded, and loops, are converted into simple labels. String literal constants are allocated into a global interning table. This LIR is passed to the backend of the compiler for codegen targeting a specific platform.

## Backend

Once the compiler has generated a platform independent LIR, the backend of the compiler can take the last required steps for building our executable. 

### Codegen

Here, assembly for our target platform is generated. Registers are allocated, and stack variables can potentially be optimized away. Constant and static data segments are allocated, and the final assembly for each instruction is serialized. Depending on the options passed to the compiler, this may be the last step if only assembly is desired. However, most of the time we will continue to the assembling and linking steps.

### Assembling

In this step we use the generated assembly and invoke the assembler for the target platform to create our object code.

### Linking

Finally, our object code can be linked with the C standard library (and potentially with other libraries) by invoking the linker for the target platform, and creating our final executable. We are now finished compiling our program! 🥳
