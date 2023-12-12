#  Type Soundness of the Base+Overlap+Lazy λ*-Calculus in Coq with Syntactic Qualifiers

## Variant

Here archives the different varients of lambda star system implemented with syntactic qualifiers. The mechanization follows the same pattern as the corresponding version with set qualifiers except for a rebase on syntactic qualifiers. The affixes of the sub-directory indicates the following features:

* [`lazy`] -- Term typing assigns _minimal_ qualifiers instead of transitivity closed ones. If we do eager qualifier assignments, i.e. always assign saturated qualifiers, then mapping to set qualifiers is not necessary due to nature saturation.
* [`syntactic`] -- The system is implemented with syntactic qualifiers.
* [`widapp`] -- The system do not require precise intersection in the application rule. Instead, it requires saturated upper bounds for argument qualifiers `d1` and function qualifiers `df`, and saturated lower bounds for the function domain qualifier (the intersection qualifiers). This feature allows future development on call-dependent qualifiers because we can evaluate to upper bounds and lower bounds from syntactic qualifiers to normal qualifiers to use mapping to set qualifiers.



## Syntactic Qualifiers

The syntactic qualifier design does not allow intersection, so the syntactic qualifier cannot directly encode the overlap qualifier in the application rule. 

The advantage of removing intersection in syntactic qualifier rules is that the qualifier can only grow monotonicly, which removes unnecessary overhead for handling the combination of intersection and union (distributive law of intersection and union is not allowed here, i.e. `v : (a | b) & (a | c)`, derives `v` has both type `a | b` and `a | c`, which is not possible). 