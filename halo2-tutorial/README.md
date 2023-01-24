# Halo2 Tutorial

This repo includes a few simple examples to show how to write circuit in Halo2.

## Instruction

Compile the repo

```
cargo build
```

Run the examples
```
fibo (n) = fibo (n-1) + fibo(n-2) s.t fibo(0) = 1, fibo(1)=1
cargo run --bin example1
cargo run --bin example2

fib(i] = fib(i - 3) + (fib(i - 2) ^ fib(i - 1]); s.t fibo(0) = 1, fibo(1)=3, fibo(2) = 2 

cargo run --bin example3
```
