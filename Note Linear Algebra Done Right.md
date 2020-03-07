<style type="text/css">
    h1 { counter-reset: h2counter; }
    h2 { counter-reset: h3counter; }
    h3 { counter-reset: h4counter; }
    h4 { counter-reset: h5counter; }
    h5 { counter-reset: h6counter; }
    h6 { }
    h2:before {
      counter-increment: h2counter;
      content: counter(h2counter) ".\0000a0\0000a0";
    }
    h3:before {
      counter-increment: h3counter;
      content: counter(h2counter) "."
                counter(h3counter) ".\0000a0\0000a0";
    }
    h4:before {
      counter-increment: h4counter;
      content: counter(h2counter) "."
                counter(h3counter) "."
                counter(h4counter) ".\0000a0\0000a0";
    }
    h5:before {
      counter-increment: h5counter;
      content: counter(h2counter) "."
                counter(h3counter) "."
                counter(h4counter) "."
                counter(h5counter) ".\0000a0\0000a0";
    }
    h6:before {
      counter-increment: h6counter;
      content: counter(h2counter) "."
                counter(h3counter) "."
                counter(h4counter) "."
                counter(h5counter) "."
                counter(h6counter) ".\0000a0\0000a0";
    }
</style>

# Linear Algebra Done Right
## C1
### properties of complex arithmetic
![complex properties](figure/1_3_complex_properties.png)
![substraction, division](figure/1_5_complex_sub.png)

$ F=R\cup C$
Elements of F are called scalars.
A list of length n = an n-tuple.
A list of length 0: ().

$ F^n $ is the set of lists of length n of elements of $F$:
$$ F^n=\{(x_1,\cdots,x_n):x_j\in F\ for\ j=1,\cdots,n\} $$
$x_j$is the $j^{th}$ coordinate of $(x_1,\cdots,x_n)$.
0 denotes the list of length n whose coor are all 0

scalar multiplication in $F^n$
$$ \lambda (x_1,\cdots,x_n)=(\lambda x_1, \cdots,\lambda x_n) $$
here $ \lambda \in F$ and $x\in F^n $

### field

### Definition of Vector Space
The motivation for the definition of a vector space comes from properties of addition and scalar multiplication in $F^n$: 
* Addition is commutative, associative, and has an identity. Every element has an additive inverse.
* Scalar multiplication is associative. Scalar multiplication by 1 acts as expected.

![Definition of vector space](figure/1_19_vector_space.png)
$R^n$ is a vector space over $R$, and $C^n$ is a vector space over $C$.
Elements of a vector space are called vectors or points.
![F^S](figure/1_23_F^S.png)
![F^S](figure/1_24_F^S_vector_space.png)


$F^n$ and $F^\infty$, are special cases of the vector space $F^S$
we can think of $F^n$ as $F^{\{1,2,\cdots,n\}}$.
#### Unique additive inverse and identity inverse
A vector space has a unique additive identity.
Every element in a vector space has a unique additive inverse.

Because additive inverses are unique, the following notation now makes sense:
* $-v$ denotes the additive inverse of $v$
* $w - v$ is defined to be $w +(-v)$.

declaration once and for all:
$V$ denotes a vector space over $F$.
0 denotes a scalar (the number $0\in F$) on the left side of the equation and a vector (the additive identity of $V$) on the right side of the equation.
$$ 0v = 0,\forall v \in V. $$
Proof.
$$ 0v = (0 + 0)v = 0v + 0v $$
The only part of the definition of a vector space that connects scalar multiplication and vector addition is the distributive property. Thus the distributive property must be used in the proof.

$$ a0 = 0, \forall a \in F $$
$$(-1)v = -v,\forall v \in V $$

### subspace
A subset U of V is called a subspace of V if U is also a vector space (using the same addition and scalar multiplication as on V).

Example $\{(x1,x2,0):x1,x2\in F\}$ is a subspace of $F^3$

linear subspace = subspace
![Conditions for a subspace](figure/1_34_subspace_conditions.png)

#### sum of subsets
is the set of all possible sums of elements of $U_1,U_2,\cdots,U_m$

the sum of subspaces is a subspace, and is in fact the smallest subspace containing all the summands

Sums of subspaces in the theory of vector spaces are analogous to unions of subsets in set theory.

#### direct sum
![direct sum](figure/1_40_direct_sum.png)

condition for a direct sum
$$ \sum_j u_j,\forall j,u_j\in U_j,u_j=0$$

direct sum of two subspaces
Suppose $U$ and $W$ are subspaces of $V$. Then $U + W$ is a direct sum if and only if $U \cap W=\{0\}$

## Finite-Dimensional Vector Spaces
We will usually write lists of vectors without surrounding parentheses.
### Linear Combinations and Span
linear combination of a list $v_1,\cdots,v_m$ of vectors in $V$ is a vector of the form
$$ a_1v_1+\cdots+a_mv_m $$
where $a_i\in F$
$ span(v_1,\cdots,v_m)=\{ a_1v_1 +\cdots+ a_mv_m:a_i\in F\} $
linear span = span
The span of a list of vectors in V is the smallest subspace of V containing all the vectors in the list.
If $span(v_1,\cdots,v_m)=V$, we say that $v_1,\cdots, v_m$ spans $V$.
A vector space is called finite-dimensional if some list of vectors in it spans the space.
Recall that by definition every list has finite length.

#### polynomial, $\mathcal{P}(F)$
![polynomial](figure/2_11_polynomial.png)
**TAKE POLYNOMIAL AS A FUNCTION!**
$\mathcal{P}(F)$ is a vector space over $F$.**WHY**
$\mathcal{P}(F)$ is a subspace of $F^F$, the vector space of functions from $F$ to $F$.

coefficients of a polynomial are uniquely determined by the polynomial. Thus:
![polynomial](figure/2_12_polynomial_degree.png)
![polynomial](figure/2_13_P_m.png)

$\mathcal{P}_m(F)=span(1,z,\cdots,z^m)$
$\mathcal{P}_m(F)$ is a finite-dimensional vector space for each nonnegative integer m.

### Linear Independence
![linear independent](figure/2_17_linearly_independent.png)
![lemma](figure/2_21_linear_dependent_lemma.png)
(b) is important.
Length of linearly independent list <= length of spanning list

### Bases
Bring the privous concept together.

A basis of V is a list of vectors in V that is linearly independent and spans V.

Every spanning list in a vector space can be reduced to a basis of the vector space.

Every finite-dimensional vector space has a basis.
* proof
By definition, a finite-dimensional vector space has a spanning list.
The previous result tells us that each spanning list can be reduced to a basis.

Every linearly independent list of vectors in a finite-dimensional vector space can be extended to a basis of the vector space.

![this](figure/2_34_subspace.png)

### Dimension
Any two bases of a finite-dimensional vector space have the same length.

The dimension of a finite-dimensional vector space is the length of any basis of the vector space.
The dimension of V (if V is finite-dimensional) is denoted by dim V.

![this](figure/2_37.png)
If V is finite-dimensional and U is a subspace of V, then dim U <= dim V.

Suppose V is finite-dimensional. Then every linearly independent list of vectors in V with length dim V is a basis of V.

Suppose V is finite-dimensional. Then every spanning list of vectors in V with length dim V is a basis of V.

If U1 and U2 are subspaces of a finite-dimensional vector space, then 
$$ dim(U_1 + U_2)=dim U_1 + dim U_2 - dim(U1 \cap U2) $$

## Linear Maps
No one gets excited about vector spaces. The interesting part of linear algebra is the subject to which we now turn—linear maps.

V and W denote vector spaces over F
### The Vector Space of Linear Maps
#### Definition and Examples of Linear Maps
linear transformation = linear maps
![linear map](figure/3_2.png)
notation: $ T(v)=Tv $

The set of all linear maps from V to W is denoted $ \mathcal{L}(V,W) $

examples of linear maps:
* zero
$$ 0v=0 $$
The 0 on the left side of the equation above is a function from V to W, whereas the 0 on the right side is the additive identity in W.

* identity
$$ Iv=v $$
is the function on some vector space that takes
each element to itself

* differentiation
$$ Dp=p^\prime $$
$(f + g)^\prime = f^\prime + g^\prime$ and $(\lambda f)^\prime=\lambda f^\prime$ whenever $f, g$ are differentiable and $\lambda$ is a constant

* integration
$$ Tp=\int^1_0 p(x)dx $$
the integral of the sum of two functions equals the sum of the integrals, and the integral of a constant times a function equals the constant times the integral of the function

The existence part of the next result means that we can find a linear map that takes on whatever values we wish on the vectors in a basis. 
The uniqueness part of the next result means that a linear map is completely determined by its values on a basis.
* 3.5
![this](figure/3_5.png)

Proof. Important! See P70.

### Algebraic Operations on $\mathcal{L}(V,W)$
![this](figure/3_6.png)
With the operations of addition and scalar multiplication as defined above, $\mathcal{L}(V,W)$ is a vector space

![this](figure/3_8.png)
![this](figure/3_9.png)

Multiplication of linear maps is not commutative.

Suppose T is a linear map from V to W. Then $T(0)=0$.

### Null Spaces and Ranges
#### Null Space and Injectivity
kernel = null space
$null T=\{v\in V: Tv=0\}$
If T is the zero map from V to W, in other words if Tv = 0 for every v $\in$ V, then null T = V

Suppose $T\in \mathcal{L}(V,W)$. Then null T is a subspace of V.

A function $T: V \rightarrow W$ is called **injective** if $Tu = Tv$ implies $u = v$.
one-to-one = injective, T is injective if it maps distinct inputs to distinct outputs

* 3.16
Let $T\in \mathcal{L}(V,W)$. Then T is injective if and only if null T = {0}.

#### Range and Surjectivity
range = image
$ range\ T =\{Tv: v\in V\} $
If T is the zero map from V to W, in other words if Tv = 0 for every $v \in V$, then range T = {0}

If $T\in \mathcal{L}(V,W)$, then range T is a subspace of W.

A function $T: V\rightarrow W$ is called **surjective** if its range equals W.
surjective=onto

#### Fundamental Theorem of Linear Maps
Suppose V is finite-dimensional and $T: V \in \mathcal{L}(V,W)$. Then range T is finite-dimensional and 
$$dim\ V = dim\ null\ T + dim\ range\ T$$

Suppose V and W are finite-dimensional vector spaces such that dimV > dimW. Then no linear map from V to W is injective.

Suppose V and W are finite-dimensional vector spaces such that dimV < dimW. Then no linear map from V to W is surjective.

Homogeneous (齐次的), in this context, means that the constant term on the right side of each equation below is 0.

A homogeneous system of linear equations with more variables than equations has nonzero solutions./null T is strictly bigger than {0} / T is not injective
* range T={0}

An inhomogeneous system of linear equations with more equations than variables has no solution for some choice of the constant terms. range T is not equal to Fm / T is not surjective

### Matrices
#### Representing a Linear Map by a Matrix
the key definition in this section
* 3.32 Definition matrix of a linear map
![this](figure/3_32.png)
![this](figure/3_32_1.png)

#### Addition and Scalar Multiplication of Matrices
* 3.36 The matrix of the sum of linear maps
Suppose $S, T \in \mathcal{L}(V,M)$. Then $\mathcal{M}(S + T)=\mathcal{M}(S)+\mathcal{M}(T)$

* 3.38 The matrix of a scalar times a linear map
Suppose $S, T \in \mathcal{L}(V,M)$. Then $\mathcal{M}(\lambda T)=\lambda \mathcal{M}(T)$

* 3.39 Notation $F^{m,n}$
For m and n positive integers, the set of all m-by-n matrices with entries in F is denoted by $F^{m,n}$.

* 3.40 dim $F^{m,n}=mn$
Suppose m and n are positive integers. With addition and scalar multiplication defined as above, $F^{m,n}$ is a vector space with dimension mn.

In the following result, the assumption is that **the same basis of V** is used in considering $T\in \mathcal{L}(U,V)$ and $S\in \mathcal{L}(V,W)$, **the same basis of W** is used in considering $S\in \mathcal{L}(V,W)$ and $ST\in \mathcal{L}(U,W)$, and **the same basis of U** is used in considering $T\in \mathcal{L}(U,V)$ and $ST\in \mathcal{L}(U,W)$.
* 3.43 The matrix of the product of linear maps
If $T\in \mathcal{L}(U,V)$ and $S\in \mathcal{L}(V,W)$, then $\mathcal{M}(ST)=\mathcal{M}(S)\mathcal{M}(T)$

Understanding:
It is us who define the multiplication of Matrix. We select matrix to express linear transformation. We find a way to express the combination of linear maps, that is the multiplication of matrices.

* 3.47 Entry of matrix product equals row times column
$$(AC)_{j,k}=A_{j,\cdot}C_{\cdot,k}$$

* 3.49 Column of matrix product equals matrix times column
$$(AC)_{\cdot,k}=AC_{\cdot,k}$$

* 3.52
![this](figure/3_52.png)

### Invertibility and Isomorphic Vector Spaces
* 3.56 Invertibility is equivalent to injectivity and surjectivity
A linear map is invertible if and only if it is injective and surjective.

* 3.58 Definition isomorphism, isomorphic
  * An isomorphism (同构体) is an invertible linear map.
  * Two vector spaces are called isomorphic if there is an isomorphism from one vector space onto the other one.

The terms “isomorphism” and “invertible linear map” mean the same thing.

The Greek word isos means equal; the Greek word morph means shape. Thus isomorphic literally means equal shape.

* 3.59 Dimension shows whether vector spaces are isomorphic
Two finite-dimensional vector spaces over F are isomorphic if and only if they have the same dimension.

* 3.61 $ dim\ \mathcal{L}(V,W)=(dim\ V)(dim\ W)$

#### Linear Maps Thought of as Matrix Multiplication
Previously we defined the matrix of a linear map. Now we define the matrix of a vector.
![this](figure/3_62.png)
The matrix depends of a vector depends on the basis of V.
The basis of V must be sure.

![this](figure/3_64.png)

* 3.65 Linear maps act like matrix multiplication
  ![this](figure/3_65.png)

keep in mind that the specific matrix A depends not only on the linear map but also on the choice of bases. One of the themes of many of the most important results in later chapters will be the choice of a basis that makes the matrix A as simple as possible.

In this book, we concentrate on linear maps rather than on matrices. However, sometimes thinking of linear maps as matrices (or thinking of matrices as linear maps) gives important insights that we will find useful.

* 3.67 Definition operator
  * A linear map from a vector space to itself is called an operator.
  * The notation $\mathcal{L}(V)$ denotes the set of all operators on V. In other words, $\mathcal{L}(V)=\mathcal{L}(V,V)$.

the next result is remarkable—it states that for operators on a finite-dimensional vector space, either injectivity or surjectivity alone implies the other condition. Often it is easier to check that an operator on a finite-dimensional vector space is injective, and then we get surjectivity for free.
* 3.69 Injectivity is equivalent to surjectivity in finite dimensions
Suppose V is finite-dimensional and $T\in \mathcal{L}(V)$. Then the following are equivalent:
(a) T is invertible;
(b) T is injective;
(c) T is surjective.

### Products and Quotients of Vector Spaces
#### Products of Vector Spaces
As usual when dealing with more than one vector space, all the vector spaces in use should be over the same field.

* 3.71 Definition product of vector spaces
  ![this](figure/3_71.png)
  

* 3.73 Product of vector spaces is a vector space

![this](figure/3_74.png)

* 3.76 Dimension of a product is the sum of dimensions
  ![this](figure/3_76.png)


#### Products and Direct Sums
* 3.77 Products and direct sums
  ![this](figure/3_77.png)

* 3.78 A sum is a direct sum if and only if dimensions add up
  ![this](figure/3_78.png)

#### Quotients of Vector Spaces
* 3.79 Definition v + U
  ![this](figure/3_79.png)

* 3.81 Definition affine subset, parallel
  * An affine subset of V is a subset of V of the form v + U for some $v \in V$ and some subspace U of V.
  * For $v \in V$ and U a subspace of V, the affine subset $v \in U$ is said to be parallel to U.

* 3.83 Definition quotient space, V/U
  Suppose U is a subspace of V. Then the quotient space V/U is the set of all affine subsets of V parallel to U.

Following: try to make V/U a vector space
* 3.85 Two affine subsets parallel to U are equal or disjoint
  ![this](figure/3_85.png)
* 3.86 Definition addition and scalar multiplication on V=U

With definitions above:
* 3.87 Quotient space is a vector 

give us an easy way to compute the dimension of V/U
* 3.88 Definition quotient map
  ![this](figure/3_88.png)
  * The reader should verify that $\pi$ is indeed a linear map

* 3.89 Dimension of a quotient space
  * Suppose V is finite-dimensional and U is a subspace of V. Then dim V/U = dim V - dim U

* 3.90 Definition TQ
  ![this](figure/3_90.png)
* 3.91 Null space and range of T
  ![this](figure/3_91.png)

### Duality
#### The Dual Space and the Dual Map
* 3.92 Definition linear functional
A linear functional on V is a linear map from V to F. In other words, a linear functional is an element of $\mathcal{L}(V,F)$.

* 3.94 Definition dual space, $V^\prime$
The dual space of V, denoted $V^\prime$, is the vector space of all linear functionals on V. In other words, $V^\prime=\mathcal{L}(V,F)$.

* 3.95 dim V' = dim V

* 3.96 Definition dual basis
  ![this](figure/3_96.png)
* 3.97 exp
  ![this](figure/3_97.png)

* 3.98 Dual basis is a basis of the dual space

* 3.99 Definition dual map
  ![this](figure/3_99.png)

* 3.101 Algebraic properties of dual maps
  ![this](figure/3_101.png)

#### The Null Space and Range of the Dual of a Linear Map
* 3.102 Definition annihilator, 零化子
  ![this](figure/3_102.png)

* 3.105 The annihilator is a subspace
Suppose $U\subset V$. Then $U^0$ is a subspace of $V^\prime$.

* 3.106 Dimension of the annihilator
Suppose V is finite-dimensional and U is a subspace of V. Then $\dim U + \dim U^0 = \dim V$

* 3.107 The null space of $T^\prime$
  ![this](figure/3_107.png)

* 3.108 T surjective is equivalent to $T^0$ injective
  
* 3.109 The range of $T^0$
  ![this](figure/3_109.png)

* 3.110 T injective is equivalent to $T^0$ surjective

#### The Matrix of the Dual of a Linear Map
* 3.114 The matrix of $T^0$ is the transpose of the matrix of T


#### The Rank of a Matrix
* 3.117 Dimension of range T equals column rank of $\mathcal{M}(T)$
* 3.118 Row rank equals column rank

## Polynominals
### Notation
### Complex Conjugate and Absolute Value
* 4.3 Definition complex conjugate(共轭复数)

* 4.5 Properties of complex numbers
  * additivity and multiplicativity of complex conjugate
  $  \overline{w+z} =  \overline w +  \overline z $
  * multiplicativity of absolute value
    $|wz|=|w||z|$

### Uniqueness of Coefficients for Polynomials
* 4.7 If a polynomial is the zero function, then all coefficients are 0
  * The degree of the 0 polynomial is defined to be $-\infty$

### The Division Algorithm for Polynomials
If p and s are nonnegative integers, with s $\ne$ 0, then there exist nonnegative integers q and r such that
$$ p = sq + r $$

* 4.8 Division Algorithm for Polynomials
  ![this](figure/4_8.png)

### Zeros of Polynomials
* 4.9 4.10
  ![this](figure/4_9_10.png)

* 4.11 Each zero of a polynomial corresponds to a degree-1 factor
  ![this](figure/4_11.png)

* 4.12 A polynomial has at most as many zeros as its degree
  Suppose $p\in\mathcal{P}(F)$ is a polynomial with degree m >= 0. Then p has at most m distinct zeros in F.

### Factorization of Polynomials over C
* 4.13 Fundamental Theorem of Algebra
Every nonconstant polynomial with complex coefficients has a zero.

* 4.14 Factorization of a polynomial over C
* ![this](figure/4_14.png)
  
### Factorization of Polynomials over R
* 4.15 Polynomials with real coefficients have zeros in pairs
  Suppose $p\in \mathcal{P}(C)$ is a polynomial with real coefficients. If $\lambda \in C$ is a zero of p, then so is $\overline \lambda $.

Our purpose:
* 4.17 Factorization of a polynomial over R
  ![this](figure/4_17.png)

## Eigenvalues, Eigenvectors, and Invariant Subspaces
### Invariant Subspaces
Recall that an operator is a linear map from a vector space to itself.
If we have a direct sum decoomposition
$$ V=U_1+\cdots + U_m $$
where each $U_j$ is a proper subspace of V.
$ T|_{U_j} $ denotes the restriction of T to the smaller domain $U_j$


* 5.2 Definition invariant subspace
Suppose $T\in \mathcal{L}(V)$. A subspace U of V is called invariant under T if
$u \in U$ implies $Tu in U$.

* 5.3 exp
  ![this](figure/5_3.png)

#### Eigenvalues and Eigenvectors
* eigenvalues
  ![this](figure/eigenvalues.png)

* 5.6 Equivalent conditions to be an eigenvalue
  ![this](figure/5_6.png)
* 3.69 Injectivity is equivalent to surjectivity in finite dimensions
Suppose V is finite-dimensional and $T\in \mathcal{L}(V)$. Then the following are equivalent:
(a) T is invertible;
(b) T is injective;
(c) T is surjective.

* 5.10 Linearly independent eigenvectors
  ![this](figure/5_10.png)

* 5.13 Number of eigenvalues
Suppose V is finite-dimensional. Then each operator on V has at most dim V distinct eigenvalues.

#### Restriction and Quotient Operators
* 5.14 Definition $T|_U$ and $T/U$
  ![this](figure/5_14.png)

### Eigenvectors and Upper-Triangular Matrices
#### Polynomials Applied to Operators
operators can be raised to powers

* 5.17 Definition $p(T)$
  ![this](figure/5_17.png)

* 5.19 Definition product of polynomials
  ![this](figure/5_19.png)

#### Existence of Eigenvalues
* 5.21 Operators on complex vector spaces have an eigenvalue
Every operator on a finite-dimensional, nonzero, complex vector space has an eigenvalue.

#### Upper-Triangular Matrices
In Chapter 3 we discussed the matrix of a linear map from one vector space to another vector space. That matrix depended on a choice of a basis of each of the two vector spaces. Now that we are studying operators, which map a vector space to itself, **the emphasis is on using only one basis**.

* 5.22 Definition matrix of an operator
  ![this](figure/5_22.png)

Note that the matrices of operators are square arrays, rather than the more general rectangular arrays that we considered earlier for linear maps

* The $k^{th}$ column of the matrix $\mathcal{M}(T)$ is formed from the coefficients used to write $Tv_k$ as a linear combination of $v_1,\cdots,v_n$.
* You can then think of the j th column of $\mathcal{M}(T)$ as T applied to the j th basis vector

A central goal of linear algebra is to show that given an operator $T\in \mathcal{L}(V)$, there exists a basis of V with respect to which T has a reasonably simple matrix. To make this vague formulation a bit more precise, we might try to choose a basis of V such that $\mathcal{M}(T)$ has many 0’s.

* 5.24 Definition diagonal of a matrix
The diagonal of a square matrix consists of the entries along the line from the upper left corner to the bottom right corner

* 5.25 Definition upper-triangular matrix
A matrix is called upper triangular if all the entries below the diagonal equal 0.

We often use * to denote matrix entries that we do not know about or that are irrelevant to the questions being discussed.

The following proposition demonstrates a useful connection between upper-triangular matrices and invariant subspaces:
* 5.26 Conditions for upper-triangular matrix
  ![this](figure/5_26.png)

* 5.27 Over C, every operator has an upper-triangular matrix
Suppose V is a finite-dimensional complex vector space and $T\in \mathcal{L}(V)$. Then T has an upper-triangular matrix with respect to some basis of V.

* 5.30 Determination of invertibility from upper-triangular matrix
Suppose $T\in \mathcal{L}(V)$ has an upper-triangular matrix with respect to some basis of V. Then T is invertible if and only if all the entries on the diagonal of that upper-triangular matrix are nonzero.

* 5.32 Determination of eigenvalues from upper-triangular matrix
Suppose $T\in \mathcal{L}(V)$ has an upper-triangular matrix with respect to some basis of V. Then the eigenvalues of T are precisely the entries on the diagonal of that upper-triangular matrix.

### Eigenspaces and Diagonal Matrices
* 5.34 Definition diagonal matrix
A diagonal matrix is a square matrix that is 0 everywhere except possibly along the diagonal

* 5.36 Definition eigenspace, $E(\lambda, T)$
  ![this](figure/5_36.png)

The definitions imply that $\lambda$ is an eigenvalue of T if and only if $E(\lambda, T)\ne \{0\}$.

* 5.38 Sum of eigenspaces is a direct sum
  ![this](figure/5_38.png)

* 5.39 Definition diagonalizable
An operator $T\in\mathcal{L}(V)$ is called diagonalizable if the operator has a diagonal matrix with respect to some basis of V.

* 5.41 Conditions equivalent to diagonalizability
  ![this](figure/5_41.png)

Unfortunately not every operator is diagonalizable. This sad state of affairs can arise even on complex vector spaces, as shown by the next example.

* 5.44 Enough eigenvalues implies diagonalizability
If $T\in\mathcal{L}(V)$ has dim V distinct eigenvalues, then T is diagonalizable.

## Inner Product Spaces
In making the definition of a vector space, we generalized the linear structure (addition and scalar multiplication) of R2 and R3. We ignored other important features, such as the notions of length and angle. These ideas are embedded in the concept we now investigate, inner products.

### Inner Products and Norms
* 6.3 Definition inner product
  ![this](figure/6_3.png)
  * Every real number equals its complex conjugate

![this](figure/6_4.png)

* 6.5 Definition inner product space
An inner product space is a vector space V along with an inner product on V.

* 6.7 Basic properties of an inner product
  ![this](figure/6_7.png)

#### Norms
* 6.8 Definition norm
  ![this](figure/6_8.png)

* 6.10 Basic properties of the norm
Suppose $v \in V$.
(a) $\|v\| = 0$ if and only if $v = 0$.
(b) $\|\lambda v\| = |\lambda| \|v\|, \forall\lambda\in F$.

* 6.11 Definition orthogonal
  Two vectors $u, v \in V$ are called orthogonal if $\langle u, v \rangle = 0$.

* 6.12 Orthogonality and 0
  (a) 0 is orthogonal to every vector in V.
(b) 0 is the only vector in V that is orthogonal to itself.

* 6.13 Pythagorean Theorem
  Suppose u and v are orthogonal vectors in V. Then
  $$ \|u+v\|^2=\|u\|^2+\|v\|^2 $$

* 6.14 An orthogonal decomposition
  ![this](figure/6_14.png)

* 6.15 Cauchy–Schwarz Inequality
  ![this](figure/6_15.png)

* 6.18 Triangle Inequality
  $$ \|u+v\| \le \|u\| + \|v\| $$

* 6.22 Parallelogram Equality
  in every parallelogram, the sum of the squares of the lengths of the diagonals equals the sum of the squares of the lengths of the four sides

### Orthonormal Bases
* 6.23 Definition orthonormal
  ![this](figure/6_23.png)

* 6.25 The norm of an orthonormal linear combination
  ![this](figure/6_25.png)

* 6.26 An orthonormal list is linearly independent

* 6.27 Definition orthonormal basis
An orthonormal basis of V is an orthonormal list of vectors in V that is also a basis of V.

* 6.28 An orthonormal list of the right length is an orthonormal basis
Every orthonormal list of vectors in V with length dim V is an orthonormal basis of V.

* 6.30 Writing a vector as linear combination of orthonormal basis
  ![this](figure/6_30.png)

The algorithm used in the next proof is called the Gram–Schmidt Procedure. It gives a method for turning a linearly independent list into an orthonormal list with the same span as the original list.
* 6.31 Gram–Schmidt Procedure
  ![this](figure/6_31.png)

* 6.34 Existence of orthonormal basis
Every finite-dimensional inner product space has an orthonormal basis.

* 6.35 Orthonormal list extends to orthonormal basis
Suppose V is finite-dimensional. Then every orthonormal list of vectors in V can be extended to an orthonormal basis of V.

* 5.27 Over C, every operator has an upper-triangular matrix
Suppose V is a finite-dimensional complex vector space and $T\in \mathcal{L}(V)$. Then T has an upper-triangular matrix with respect to some basis of V.

* 6.37 Upper-triangular matrix with respect to orthonormal basis
  ![this](figure/6_37.png)

* 6.38 Schur’s Theorem
  Suppose V is a finite-dimensional complex vector space and $T\in\mathcal{L}(V)$. Then T has an upper-triangular matrix with respect to some orthonormal basis of V.

#### Linear Functionals on Inner Product Spaces
* 6.39 Definition linear functional

If $u\in V$, then the map that sends v to $\langle v,u\rangle$ is a linear functional on V.

* 6.42 Riesz Representation Theorem
  ![this](figure/6_42.png)

### Orthogonal Complements and Minimization Problems
#### Orthogonal Complements
* 6.45 Definition orthogonal complement, $U^\perp$
  ![this](figure/6_45.png)

* 6.46 Basic properties of orthogonal complement
  ![this](figure/6_46.png)

* 6.47 Direct sum of a subspace and its orthogonal complement
  Suppose U is a finite-dimensional subspace of V. Then
  $$ V=U\oplus U^\perp $$

* 6.50 Dimension of the orthogonal complement
  Suppose V is finite-dimensional and U is a subspace of V. Then $\dim U^\perp=\dim V-\dim U$

* 6.51 The orthogonal complement of the orthogonal complement
Suppose U is a finite-dimensional subspace of V. Then $U=(U^\perp)^\perp$

* 6.53 Definition orthogonal projection, $P_U$
  ![this](figure/6_53.png)
  
* 6.55 Properties of the orthogonal projection $P_U$
  ![this](figure/6_55.png)

#### Minimization Problems
The following problem often arises:
given a subspace U of V and a point v $\in$ V, find a point u $\in$ U such that $\|v-u\|$ is as small as possible.
The next proposition shows that this minimization problem is solved by taking $u=P_Uv$.

* 6.56 Minimizing the distance to a subspace
  ![this](figure/6_56.png)

* 6.58 exp
  Linear algebra has helped us discover an approximation to sin x that improves upon what we learned in calculus (better than Taylor polynomial)

## Operators on Inner Product Spaces
### Self-Adjoint and Normal Operators
#### Adjoints
* 7.2 伴随矩阵
  ![this](figure/7_2.png)

By the Riesz Representation Theorem (6.42), there exists a unique vector in V such that this linear functional is given by taking the inner product with it. We call this unique vector $T^*w$

* 7.5 The adjoint is a linear map

* 7.6 Properties of the adjoint
  ![this](figure/7_6.png)

The next result shows the relationship between the null space and the range of a linear map and its adjoint.

* 7.7
  ![this](figure/7_7.png)

* 7.8 Definition conjugate transpose 共轭转置
  The conjugate transpose of an m-by-n matrix is the n-by-m matrix obtained by interchanging the rows and columns and then taking the complex conjugate of each entry.

The adjoint of a linear map does not depend on a choice of basis. This explains why this book emphasizes adjoints of linear maps instead of conjugate transposes of matrices.

* 7.10 The matrix of $T^*$
  ![this](figure/7_10.png)

#### Self-Adjoint Operators
* 7.11 Definition self-adjoint
  ![this](figure/7_11.png)

Hermitian = self-adjoint.
* 7.13 Eigenvalues of self-adjoint operators are real
Every eigenvalue of a self-adjoint operator is real.

* 7.14 Over C, T v is orthogonal to v for all v only for the 0 operator
  ![this](figure/7_14.png)

* The next result is false for real inner product spaces

* 7.15
  ![this](figure/7_15.png)
  
* 7.16
  ![this](figure/7_16.png)
  After adding the condition of self-adjoint, $\langle Tv,v \rangle$<=>$T=0$

#### Normal Operators
* 7.18 Definition normal (正规)
  ![this](figure/7_18.png)
  Obviously every self-adjoint operator is normal, because if T is self-adjoint then $T^*=T$.

* 7.20
  ![this](figure/7_20.png)

* 7.21 For T normal, T and $T^*$ have the same eigenvectors
  ![this](figure/7_21.png)

* 7.22
  ![this](figure/7_22.png)

### The Spectral Theorem
The Spectral Theorem is probably the most useful tool in the study of operators on inner product spaces

#### The Complex Spectral 
* 7.24 Complex Spectral Theorem
  ![this](figure/7_24.png)

#### The Real Spectral Theorem
* 7.26 Invertible quadratic expressions
  ![this](figure/7_26.png)

* 7.27 Self-adjoint operators have eigenvalues

* 7.28
  ![this](figure/7_28.png)

* 7.29 Real Spectral Theorem
  ![this](figure/7_29.png)

### Positive Operators and Isometries
#### Positive Operators
* 7.31
  ![this](figure/7_31.png)
  If V is a complex vector space, then the requirement that T is self-adjoint can be dropped from the definition above

* 7.35 Characterization of positive operators
  ![this](figure/7_35.png)

* positive semidefinite operator=positive operator, (so here replacing "positive" with "nonnegative" will be more proper but we get used to the custom)

Each nonnegative number has a unique nonnegative square root. The next result shows that positive operators enjoy a similar property.
* 7.36 Each positive operator has only one positive square root

#### Isometries (等距的)
* 7.37 Definition isometry
  ![this](figure/7_37.png)

The Greek word isos means equal; the Greek word metron means measure. Thus isometry literally means equal measure.

An isometry on a real inner product space is often called an orthogonal operator. An isometry on a complex inner product space is often called a unitary operator
* 7.42 Characterization of isometries
  ![this](figure/7_42.png)

The previous result shows that every isometry is normal [see (a), (e), and (f) of 7.42]. Thus characterizations of normal operators can be used to give descriptions of isometries

* 7.43 Description of isometries when F D C
  ![this](figure/7_43.png)

### Polar Decomposition and Singular Value Decomposition
#### Polar Decomposition
Recall our analogy between C and $\mathcal{L}(V)$. 
Under this analogy, 
1. a complex number $z$ corresponds to an operator $T$, and $\bar z$ corresponds to $T^*$. 
2. the real numbers ($z = \bar z$) correspond to the self-adjoint operators ($T = T^*$)
3. the nonnegative numbers correspond to the (badly named) positive operators.
4. $z\bar z=1$ <==> $T^*T=I$, the unit circle in C corresponds to the isometries
5. $z=\cfrac{z}{|z|}|z|=\cfrac{z}{|z|}\sqrt{\bar{z}z}$ <==> $T=S\sqrt{T*T}$

The Polar Decomposition (7.45) states that each operator on V is the product of an isometry and a positive operator
**Warning**: S may require one orthonormal basis and $\sqrt{T^*T}$ may require a different orthonormal basis

#### Singular Value Decomposition
* 7.49 Definition singular values
  ![this](figure/7_49.png)

Each $T\in\mathcal{L}(V)$ has dim V singular values

When we worked with linear maps from one vector space to a second vector space, we considered the matrix of a linear map with respect to a basis of the first vector space and a basis of the second vector space. When dealing with operators, which are linear maps from a vector space to itself, we almost always use only one basis, making it play both roles.

The Singular Value Decomposition allows us a rare opportunity to make good use of two different bases for the matrix of an operator

In other words, every operator on V has a diagonal matrix with respect to some orthonormal bases of V, provided that we are permitted to use two different bases rather than a single basis as customary when working with operators.

* 7.52 Singular values without taking square root of an operator
  ![this](figure/7_52.png)

## Operators on Complex Vector Spaces
### Generalized Eigenvectors and Nilpotent Operators
#### Null Spaces of Powers of an Operator
* 8.3 Equality in the sequence of null spaces
  ![this](figure/8_3.png)

* 8.4 Null spaces stop growing
  ![this](figure/8_4.png)

* 8.5
  ![this](figure/8_5.png)

#### Generalized Eigenvectors
* 8.9 Generalized Eigenvectors
  ![this](figure/8_9.png)

* 8.10 Definition generalized eigenspace, $G(\lambda, T)$
  ![this](figure/8_10.png)

* 8.11 Description of generalized eigenspaces
  ![this](figure/8_11.png)

* 8.13
  ![this](figure/8_13.png)

#### Nilpotent Operators (幂零的)
* 8.16 Definition nilpotent
An operator is called nilpotent if some power of it equals 0.

* 8.18
  ![this](figure/8_18.png)

* 8.19 Matrix of a nilpotent operator
  ![this](figure/8_19.png)

### Decomposition of an Operator
#### Description of Operators on Complex Vector Spaces
* 8.20 The null space and range of p(T) are invariant under T
  ![this](figure/8_20.png)

* 8.21
  ![this](figure/8_21.png)

#### Multiplicity of an Eigenvalue
* 8.24
  ![this](figure/8_24.png)

* 8.26 Sum of the multiplicities equals dim V

The terms algebraic multiplicity and geometric multiplicity are used in
some books. In case you encounter this terminology, be aware that the
algebraic multiplicity is the same as the multiplicity defined here and the
geometric multiplicity is the dimension of the corresponding eigenspace.

### Block Diagonal Matrices
* 8.27
  ![this](figure/8_27.png)

* 8.29
  ![this](figure/8_29.png)

#### Square Roots
Every complex number has a square root, but not every operator on a complex vector space has a square root

* 8.31
  ![this](figure/8_31.png)

the next result holds only on complex vector spaces
* 8.33
  ![this](figure/8_33.png)

### Characteristic and Minimal Polynomials
#### The Cayley–Hamilton Theorem
* 8.34 Definition characteristic polynomial
  ![this](figure/8_34.png)

* 8.36 Degree and zeros of characteristic polynomial
  ![this](figure/8_36.png)

Most texts define the characteristic polynomial using determinants (the two definitions are equivalent by 10.25). The approach taken here, which is considerably simpler, leads to the following easy proof of the Cayley–Hamilton Theorem

* 8.37 Cayley–Hamilton Theorem
  ![this](figure/8_37.png)

#### The Minimal Polynomial
* 8.38 Definition monic polynomial
  A monic polynomial is a polynomial whose highest-degree coefficient equals 1

* 8.40 Minimal polynomial
  Suppose $T\in\mathcal{L}(V)$. Then there is a unique monic polynomial p of smallest degree such that $p(T)=0$.

* 8.43 Definition minimal polynomial
  ![this](figure/8_43.png)

The Cayley–Hamilton Theorem (8.37) tells us that if V is a complex vector space, then the minimal polynomial of each operator on V has degree at most dim V. This remarkable improvement also holds on real vector spaces, as we will see in the next chapter.

* 8.46 $q(T)=0$ implies q is a multiple of the minimal polynomial
  ![this](figure/8_46.png)

The next result is stated only for complex vector spaces, because we have not yet defined the characteristic polynomial when F D R. However, the result also holds for real vector spaces, as we will see in the next chapter.

* 8.48 Characteristic polynomial is a multiple of minimal polynomial
  ![this](figure/8_48.png)

* 8.49 Eigenvalues are the zeros of the minimal polynomial

### Jordan Form
* 8.59 Definition Jordan basis
  ![this](figure/8_59.png)

* 8.60 Jordan Form
Suppose V is a complex vector space. If $T\in\mathcal{L}(V)$, then there is a basis of V that is a Jordan basis for T.

## Operators on Real Vector Spaces
* 9.2 Definition complexification of V, $V_C$
  ![this](figure/9_2.png)

* 9.4 Basis of V is basis of $V_C$
  The dimension of $V_C$ (as a complex vector space) equals the dimension of V (as a real vector space).

#### Complexification of an Operator
* 9.5 Definition complexification of T, $T_C$
  ![THIS](figure/9_5.png)
  $T_C(\lambda(u+iv))=\lambda T_C(u+iv),\forall u,v\in V, \lambda \in C$

* 9.7 Matrix of $T_C$ equals matrix of T

* 9.8 Every operator has an invariant subspace of dimension 1 or 2

#### The Minimal Polynomial of the Complexification
* 9.10 Minimal polynomial of $T_C$ equals minimal polynomial of T

#### Eigenvalues of the Complexification
* 9.11
  ![this](figure/9_11.png)

* 9.16 Nonreal eigenvalues of $T_C$ come in pairs
  if a number is an eigenvalue of $T_C$, then its complex conjugate is also an eigenvalue of $T_C$

* 9.19 Operator on odd-dimensional vector space has eigenvalue

#### Characteristic Polynomial of the Complexification
* 9.20
  ![this](figure/9_20.png)

* 9.21
  ![this](figure/9_21.png)

### Operators on Real Inner Product Spaces
#### Normal Operators on Real Inner Product Spaces
#### Isometries on Real Inner Product Spaces

## Trace and Determinant
nonsingular=invertible
singular=noninvertible

* 10.7 Change of basis formula
  ![this](figure/10_7.png)

### Change of Basis
### Trace: A Connection Between Operators and Matrices
* 10.9 Definition trace of an operator
  ![this](figure/10_9.png)

The trace has a close connection with the characteristic polynomial
* 10.12 Then trace T equals the negative of the coefficient of $z^{n-1}$ in the characteristic polynomial of T.

* 10.15 Trace of matrix of operator does not depend on basis
  ![this](figure/10_15.png)

* 10.16 Trace of an operator equals trace of its matrix

* 10.19 The identity is not the difference of ST and TS

### Determinant
#### Determinant of an Operator
* 10.23
  ![this](figure/10_23.png)

* 10.24 Invertible is equivalent to nonzero determinant

#### Determinant of a Matrix
Unlike the trace, det T need not equal the product of the diagonal entries

* 10.27 Definition permutation, perm n
  ![this](figure/10_27.png)
  
* 10.40 Determinant is multiplicative

* 10.41 Determinant of matrix of operator does not depend on basis
  * same as the trace

* 10.44 Determinant is multiplicative

#### The Sign of the Determinant
Idea: cut a piece of space into infitity blocks
* 10.52 Positive operators change volume by factor of determinant
  ![this](figure/10_52.png)
  Your intuition about volume should convince you that for a block, volume behaves the same with respect to each orthonormal basis.

* 10.53 An isometry does not change volume
  $\|Sx-Sy\|=\|S(x-y)\|=\|x-y\| $

* 10.54 T changes volume by factor of $|\det T|$