**malloc lab**



* fastbin + bins with 2**i size
* optimization on binary traces
    * set special strategy in place()
* optimization on realloc traces
    * coalesce previous and next blocks when realloc
    * set special strategy in place()



**points** : 97 = 57 (util) + 40 (thr)