# Cited exact searches (runs/varratio): commands, seeds and final summary lines

Logs are in runs/varratio/logs (gitignored); this file archives what paper.tex and RESEARCH.md cite. All runs use exact rational arithmetic.

## cubic_lc_P

```
python3 runs/varratio/cubic_lc_test.py 4 18 20 1/10,1/3,1/2,4/5,19/20,99/100 1/4,1,4,16,64 4
[05:17:22] N=18 done in 123.2s, 9000/9000 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## cubic_lc_M

```
python3 runs/varratio/cubic_lc_test.py 4 10 15 1/10,1/3,1/2,4/5,19/20,99/100 1/4,1,4,16 3 M
[05:11:10] N=10 done in 77.5s, 2520/2520 arrays, 0 not (P), 16 M<0
failure lines: 16
```

## cubic_lc_M2

```
python3 runs/varratio/cubic_lc_test.py 11 13 12 1/10,1/2,9/10,19/20,99/100 1,4 6 M
[05:21:11] N=13 done in 77.1s, 360/360 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## cubic_lc_big24

```
python3 runs/varratio/cubic_lc_test.py 24 24 6 1/2,9/10,19/20,99/100 1,4,16 5
[05:18:25] N=24 done in 4.6s, 72/72 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## cubic_lc_big32

```
python3 runs/varratio/cubic_lc_test.py 32 32 6 1/2,9/10,19/20,99/100 1,4,16 32
[05:18:27] N=32 done in 7.3s, 72/72 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## cubic_lc_big48

```
python3 runs/varratio/cubic_lc_test.py 48 48 6 1/2,9/10,19/20,99/100 1,4,16 48
[05:19:05] N=48 done in 44.5s, 72/72 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## cubic_lc_big64

```
python3 runs/varratio/cubic_lc_test.py 64 64 6 1/2,9/10,19/20,99/100 1,4,16 64
[05:21:29] N=64 done in 189.3s, 72/72 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## cubic_lc_big96

```
python3 runs/varratio/cubic_lc_test.py 96 96 6 1/2,9/10,19/20,99/100 1,4,16 96
[05:36:09] N=96 done in 1069.3s, 72/72 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## G_geo_small

```
python3 runs/varratio/lcnewton_ratio_test.py 4,5,6,7,8,9,10 20 1/10,1/3,1/2,3/5,7/10,4/5,9/10,19/20,99/100 geo 11 M
[05:50:10] N=10 done in 42.3s, 1260/1260 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## G_rand_small

```
python3 runs/varratio/lcnewton_ratio_test.py 4,5,6,7,8,9,10 20 1/10,1/3,1/2,3/5,7/10,4/5,9/10,19/20,99/100 rand 12 M
[05:50:15] N=10 done in 45.4s, 1260/1260 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## G_rand_mid

```
python3 runs/varratio/lcnewton_ratio_test.py 12,14,16 12 1/10,1/3,1/2,3/5,7/10,4/5,9/10,19/20,99/100 rand 13
[05:50:09] N=16 done in 64.5s, 324/324 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## G_geo_big

```
python3 runs/varratio/lcnewton_ratio_test.py 24,40,64 6 1/2,4/5,9/10,19/20,99/100 geo 14
[05:53:49] N=40 done in 311.7s, 60/90 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## G_rand_big

```
python3 runs/varratio/lcnewton_ratio_test.py 24,40,64 6 1/2,4/5,9/10,19/20,99/100 rand 15
[05:54:28] N=40 done in 347.9s, 60/90 arrays, 0 not (P), 0 M<0
failure lines: 0
```

## NP_16

```
python3 runs/varratio/newton_product_lc.py 16 4000 99
N=16: 0/4000 products not log-concave
failure lines: 0
```

## NP trials at N = 4, 6, 10 (3000 each, seeds 4, 6, 10)

```
N=4: 0/3000 products not log-concave
N=6: 0/3000 products not log-concave
N=10: 0/3000 products not log-concave
```
