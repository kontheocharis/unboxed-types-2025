
Okay so to reproduce QTT we need:

1. A CWF for irrelevant data:

LTT - layout type theory syntactic CWF

So,
    
We must have:

    TyLTT : (Γ : ConLTT) → {_ : Is0 Γ} → Layout Γ → Set
    |_| : TyLTT Γ b → TyLTT Γ 0

Predicate on contexts being zero-sized:

    Is0 : ConLTT → Set
    Is0 • = ⊤
    Is0 (Γ . {a} A) = Is0 Γ × (a = 0)
    
Make a context zero-sized:

    0 : ConLTT → ConLTT
    0 ∙ = ∙
    0 (Γ . {a} A) = 0 Γ . |A|
    
    -- functorial action uses ||_||
    0 : SubLTT Γ Δ → SubLTT (0 Γ) (0 Δ)
    ...
    
    0is0 : forall Γ . Is0 (0 Γ)
    ...
    
    forget : SubLTT Γ (0 Γ)
    forget {Γ = ∙} = !
    forget {Γ = Γ.A} = (forget {Γ} . p, ||q||) : SubLTT Γ.A (0 Γ . |F A|)

Semiring:

    R = {0, ω}

Un-resourced:

    C = {
        |C| = (Γ : ConLTT) × Is0 Γ
        C((Γ, p), (Δ, q)) = SubLTT Γ Δ
    }

    Ty (Γ, p) = TyLTT Γ {p} 0
    Tm (Γ, p) A = TmLTT Γ |A|

Substitution is closed under 0 types and 0 contexts:

    -[-]0 : {0 Γ, 0 Δ} → TyLTT Δ 0 → SubLTT Γ Δ → TyLTT Γ 0
    -[-]0 : {0 Γ, 0 Δ} → TmLTT Δ |A| → (σ : SubLTT Γ Δ) → TmLTT Γ (|A[σ]0|)

this should follow from the more general fact that layouts are stable under substitution.

    -[-] : Layout Δ → SubLTT Γ Δ → Layout Γ
    0[σ] = 0  <-- this is the crucial thing
    1[σ] = 1 
    ptr[σ] = ptr
    size[σ] = size
    (a + b)[σ] = a[σ] + b[σ]
    (n * b)[σ] = n[σ] + b[σ]
                 here n : TmLTT Γ nat (or partially static if you wish)


    S : TyLTT Δ 0,  p : Is0 Γ,  q : Is0 Δ
    --------------------------
    (p, refl) : Is0 Γ.S
    SubLTT(Γ, Δ.S) ≃  (σ : SubLTT(Γ, Δ)) × TmLTT Γ S[σ]   already given
    S[σ] : TyLTT Γ 0   by substitution

    OK


Resourced:

    L = {
        |L| = ConLTT
        C(Γ, Δ) = SubLTT Γ Δ
    }

    U : L → C
    U (Γ : ConLTT) = (0 Γ, 0is0)
    
    (+) : L ×C L → L
    Γ + Γ' where p : 0 Γ = 0 Γ'
        =  Γ   -- first projection functor
    U (Γ + Γ') = U Γ = U Γ'  OK
    
    ∘ : |L|
    ∘ = ∙

    ρ(_) : L → L
    0(Γ) = 0 Γ
    ω(Γ) = Γ


Resourced terms are just LTT terms.

    RTm Γ S = TmLTT Γ S
    
U on terms defined by induction on syntax
This *must* be injective, which is only possible if `|_|` is injective.

    U-inj : U x = U y → x = y
    
Injective up to internal equality.

Proof strategy: for each `let ||x'|| = U x in M`, invoke the `||-elim`
    
         elim-|| (\x => let ||x'|| = x in M) (\x => ?) U x
         
         where ? : let ||x'|| = ||x|| in M
                        = M[x'/x]
         
thereby cancelling using `||x'||`. This must be done both for `x` and `y`.
The goal is refined to `M[x'/x][y'/y]` in which case we should be
able to proceed by induction on `x` and `y`?
    

    U : TmLTT Γ S → TmLTT (0 Γ) |S|
    U (||a||) = ||U a||
    U (code A) = ||code A||
    U (||-elim P p a)
        = let ||p'|| = U p in
          let ||a'|| = U a in
          || ||-elim P (x . p' (|| x ||)) a' ||
    U (lam (f : Tm Γ.A B))
        = let ||f' : Tm (0 Γ).|A| B|| = U f in
        || lam (x . f' (|| x ||)) ||
    U (app u v)
        = let ||u' : Tm (0 Γ) (Π A B)|| = U u
        in let ||v'|| = v in ||app u' v'||
    ...

    U : SubLTT Γ (0 Δ) → SubLTT (0 Γ) (0 Δ)
    U {Δ = ∙} ! = !
    U {Δ = (Δ, A)} (σ, t) = (U σ, U t)

Resourced context structure is just context structure of LTT


It is probably easiest to have explicit coercions. What do the normal forms say? every non-neutral of type `|X|` is `||x||` for some `x : X`. If this is true then `U` is injective?


Question for Bob Atkey: what is the significance of the faithfulness of U? -- only thing remaining to show I think