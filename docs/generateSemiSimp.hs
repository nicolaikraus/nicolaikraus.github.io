-- This file can be used to generate the Agda definitions of (truncated) semi-simplicial types. For explanations, see the accompanying Agda file.
-- For general explanations of the problem, see 
-- http://uf-ias-2012.wikispaces.com/Semi-simplicial+types

-- Caveat: This is a rather ugly ad-hoc implementation. A better way to do this would be to use Haskell's packages for Agda's Syntax and generate the abstract syntax tree before printing it nicely.

-- The main function is the following.
-- generateAll n will, for some number n, generate the types of semi-simplicial "standard" simplices Xi (together with their boundaries, here called 'Pi').
-- Putting the output into the Agda file Semisimplicial.agda allows to check whether everything type checks (it works with Agda 2.3.3 and probably most other versions, as I do not use any special features at all and not even any kind of library)

generateAll n = generateAllAux n 0



-- The actual construction (for explanations, see the Agda file).
-- First: generate the list [ λ (gj : (S j) ⇒+ (S k)) . x_j(fk ∘+ gj)]_{j : Fin k} with a "*" (unique element of the unit type) in the end. 

genArgsAux k j =
  if k == j 
    then "*"
    else "(λ (g" ++ (show j) ++ " : (S " ++ (show j) ++ ") ⇒+ (S " ++ (show k) ++ ")) " ++
         "→ x" ++ (show j) ++ "(f" ++ (show k) ++ " ∘+ g" ++ (show j) ++ ")) , " ++ (genArgsAux k (j + 1))

genArgs k = genArgsAux k 0



genSkelAux n k = 
  if k == n 
    then "⊤" 
    else "Σ ((f" ++ (show k) ++ " : (S " ++ (show k) ++ ") ⇒+ (S " ++ (show n) ++ ")) " ++ 
                                             "→ X" ++ (show k) ++ " (" ++ genArgs k ++ "))" ++ 
         "  λ x" ++ (show k) ++ " → " ++ (genSkelAux n (k+1)) ++ " "

genSkel n = genSkelAux n 0


genP n = ("P" ++ (show n) ++ " = " ++ genSkel n)

genXty n = "X" ++ (show n) ++ " : P" ++ (show n) ++ " → Type"
genXtm n = "X" ++ (show n) ++ " = ?"

generateAllAux n k = 
  if k > n 
    then putStrLn ""
    else 
      do
        putStrLn (genP k ++ "\n\n" ++ genXty k ++ "\n" ++ genXtm k ++ "\n\n")
        generateAllAux n (k+1)




