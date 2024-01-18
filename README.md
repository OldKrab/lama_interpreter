# Сборка

Для сборки, запуска тестов и теста производительности выполните `make`.

Для сборки интерпретатора выполните `make src`.

Для запуска тестов выполните `make tests`.

Для запуска теста производительности выполните `make performance`.


# Результаты теста производительности на моей машине

```
Sort
Run lama with -i
LAMA=../runtime echo "42" | `which time` -f "Sort\t%U" lamac -i Sort.lama
> Sort  6.17
Run lama with -s
LAMA=../runtime echo "42" | `which time` -f "Sort\t%U" lamac -s Sort.lama
> Sort  2.16
Compiled binary with lama
LAMA=../runtime lamac  Sort.lama && `which time` -f "Sort\t%U" ./Sort
Sort    0.30
lamac -b Sort.lama
Run my interpreter
`which time` -f "Sort\t%U" ../../src/lama_interpreter Sort.bc 
Sort    0.76
```