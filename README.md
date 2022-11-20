<h1 align="center" style="display:flex; align-items:center; justify-content:center">
    <image src="./umbrellart.svg" alt="icon"></image>
    &nbsp;
    Umbrellart
</h1>

[![codecov](https://codecov.io/gh/waynexia/umbrellart/branch/master/graph/badge.svg?token=I58Y17LSTX)](https://codecov.io/gh/waynexia/umbrellart)

An unsynchronised Adaptive Radix Tree implementation.

## Features

- [x] Associated node size
- [x] Optimistic prefix comparing
- [ ] Range scan
- [ ] Serialization

## Benchmarks

### Point Get

- 🐢 60% slower than std HashMap (16ms v.s. 10ms)
- 🚀 54% faster than std BTreeMap (16ms v.s. 30ms)

Details:
```text
sequence get umbrellart time:   [16.483 ms 16.496 ms 16.513 ms]                                    
Found 11 outliers among 100 measurements (11.00%)
  4 (4.00%) high mild
  7 (7.00%) high severe

sequence get hashmap    time:   [10.285 ms 10.385 ms 10.508 ms]                                 
Found 16 outliers among 100 measurements (16.00%)
  6 (6.00%) high mild
  10 (10.00%) high severe

sequence get btreemap   time:   [30.037 ms 30.081 ms 30.133 ms]                                  
Found 17 outliers among 100 measurements (17.00%)
  1 (1.00%) low mild
  5 (5.00%) high mild
  11 (11.00%) high severe
```

### Space efficiency

*allocation counter. data is with 1/99 sampling biases*

|            | size(bytes) | rate(compare to umbrellart) |
|------------|-------------|-----------------------------|
| corpus     | 662144      | 0.43                        |
| umbrellart | 1515938     | 1                           |
| hashmap    | 3276808     | 2.16                        |
| btreemap   | 413638      | 0.27                        |