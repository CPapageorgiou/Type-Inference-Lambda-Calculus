### Simple version of type inference for lambda terms implemented in Haskell.

### The function `derive` takes a lambda term and produces a type derivation for it, if one exists.

### For example, the term (λx.x)y can be defined as: 

### `n = Apply (Lambda "x" (Variable "x")) (Variable "y")`. 

### Then, `derive n` gives:


```
 --------------------                
 x: a , y: a |- x : a                
----------------------  -------------
y: a |- \x. x : a -> a  y: a |- y : a
-------------------------------------
        y: a |- (\x. x) y : a
```
