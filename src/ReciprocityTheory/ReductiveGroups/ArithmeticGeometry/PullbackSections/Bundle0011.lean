import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueBoundRamified
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def ChartValueBoundRamified : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
    ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
      ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
        letI := io.toAlgebra
        (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * vdP D p * (DF (T.Q.Dw j) a : ℝ) / 2)) : ℝ) : EReal) ≤
          nval Tc.V e (∑ mo ∈ P.support, P.coeff mo *
            ∏ b, C.ch.B.nabVal Tc.Fr C.ch.h T.Q.H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))

def RamifiedEigenLifts : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
    ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
      letI := io.toAlgebra
      ∃ (π : Type) (_ : Fintype π) (_ : DecidableEq π) (c : (D.host.E →+* ℂ) → π) (s : (D.host.E →+* ℂ) → Bool),
        (∀ τ, c (ComplexEmbedding.conjugate τ) = c τ ∧ s (ComplexEmbedding.conjugate τ) ≠ s τ) ∧
        ∃ (φ : Lt1 (T.Q.Dw j) → Fin (chD C.ch) → Tc.V) (ψ : Lt1 (T.Q.Dw j) → Fin (chD C.ch) → Tc.Fr),
          (∀ ℓ i, (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * vdP D p)) : ℝ) : EReal) ≤ nval Tc.V e (ψ ℓ i)) ∧
          (∀ ℓ ℓ' : Lt1 (T.Q.Dw j), ℓ'.1 ≠ ComplexEmbedding.conjugate ℓ.1 →
            ∑ i, (algebraMap Tc.V Tc.Fr (φ ℓ' i) + ψ ℓ' i - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ') i) *
              C.ch.uvec ℓ i = 0) ∧
          TB.OppositePairVanishing Tc.Fr (fun ℓ : Lt1 (T.Q.Dw j) => c ℓ.1) (fun ℓ => s ℓ.1)
            (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap Tc.V Tc.Fr (φ ℓ i) - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i))
            (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap Tc.V Tc.Fr (φ ℓ i) - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧
          TB.OppositePairVanishing Tc.Fr (fun ℓ : Lt1 (T.Q.Dw j) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ))
            (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap Tc.V Tc.Fr (φ ℓ i) - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧
          TB.OppositePairVanishing Tc.Fr (fun ℓ : Lt1 (T.Q.Dw j) => c ℓ.1) (fun ℓ => s ℓ.1)
            (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap Tc.V Tc.Fr (φ ℓ i) - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i))
            (fun ℓ => (0, ψ ℓ))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrBCField
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l) in

def BcLieAnySt : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K)
    (y : FrPt Xo c S) (τ : E →+* ℂ) (w : Sp (DualNumber K) ⟶ Xo.univ.t.G.left),
    IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w →
    ∃! a : Fin (Dw.mult τ) → K,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w

variable {Xo : Moduli Dw l} {c : Coeff l}

def bcPtAny (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (hL : BcLieAnySt Xo c) {S : Type} [CommRing S] [Algebra c.F S] {K : Type} [Field K] [Algebra c.F K]
    (ψ : S →ₐ[c.F] K) (y : FrPt Xo c S) : FrPt Xo c K where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := by
    rw [Category.assoc, y.x_over]
    unfold sOf
    rw [spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    ext r
    simp
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := tan_bc ψ.toRingHom (y.tan τ i)
  eig τ i := eig_bc ψ τ (y.eig τ i)
  basis τ w hw he := hL S K ψ y τ w hw he
  s := secCP (cpS ψ.toRingHom y.x) y.s
  gen := genBC_frame y.x hS hT ψ.toRingHom y.s y.gen

theorem frMap_bcPtAny (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (hL : BcLieAnySt Xo c) {S : Type} [CommRing S] [Algebra c.F S] {K : Type} [Field K] [Algebra c.F K]
    (ψ : S →ₐ[c.F] K) (y : FrPt Xo c S) : FrMap ψ y (bcPtAny hS hT hL ψ y) :=
  ⟨rfl, fun _ _ => rfl, bcPm ψ.toRingHom y.x, bcPm_snd _ _, bcPm_fst _ _, fun _ _ => rfl⟩

theorem frBCField_of (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (hL : BcLieAnySt Xo c) : FrBCFieldSt Xo c := by
  intro S _ _ y K _ _ ψ
  exact ⟨bcPtAny hS hT hL ψ y, frMap_bcPtAny hS hT hL ψ y⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IsMixedOver
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Mixed

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

abbrev endT (T : Over X) (φ : A ⟶ A) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ≫ φ)

def IsNormEnd (φ : A ⟶ A) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) : Prop :=
  LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (eSec A))
    (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))

def IsMixedOver (φ : A ⟶ A) (n k : ℕ) {T : Over X} (ok : (T ⟶ A) → Prop) (s : LB.Sec (LPow A L.L 1 T))
    (t₁ b : T ⟶ A) (hh : LB.Sec (LPow A L.L (k : ℤ) T)) : Prop :=
  ∃ (F₁ : LB.Sec (LPow A L.L ((n : ℤ) ^ 2) T))
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (h₁ : LB.Sec (LPow A L.L (k : ℤ) T)) (U : ThetaGrp A L.L (k : ℤ) T),
    IsVtOver A L n ok s t₁ F₁ ∧ α₀.IsGen ∧ IsNormEnd A L φ (k : ℤ) ((n : ℤ) ^ 2) α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (endT A T φ) (snd T A ≫ φ) (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ ∧
    SymLift A L.L (k : ℤ) k b U ∧ IsActOf A L.L (k : ℤ) U h₁ hh

end Mixed

abbrev kMix (D : D7) (i : Fin 2) : ℕ := D.host.g i * D.host.g (1 - i) ^ 2

def MixRootSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (n : ℕ) (x : Fin n → (T.Q.Dw j).La)
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
    ∀ (i : Fin 2) (πE : 𝓞 D.host.E), πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar πE} →
    ∃ (Tc' : CDVR) (iT : Tc.Fr →+* Tc'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : Tc.Fr, a ≠ 0 → vV Tc'.V (iT a) = (e' : ℤ) * vV Tc.V a) ∧
      ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c Tc' (iT.comp io)), yI'.IsAlg ∧
        letI := io.toAlgebra
        letI := (iT.comp io).toAlgebra
        ∃ (φ : Tc.Fr →ₐ[T.Q.c.F] Tc'.Fr)
          (F : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
            (ptO (T.Q.Xo j) yI'.1.x)))
          (t₁ bb : Fin n → (ptO (T.Q.Xo j) yI'.1.x ⟶ (T.Q.Xo j).univ.t.G))
          (hh : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((kMix D i : ℕ) : ℤ)
            (ptO (T.Q.Xo j) yI'.1.x))),
          φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1 ∧
          (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
            yI'.1.s (levPt (T.Q.Xo j) yI'.1.x (x b)) (F b)) ∧
          (∀ b, KilledBy (T.Q.Xo j) (Ideal.span {T.Q.H.bar πE}) (bb b)) ∧
          (∀ b, IsMixedOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP ((T.Q.Xo j).univ.t.act.act πE)
            (D.host.g (1 - i)) (kMix D i) (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2)) yI'.1.s (t₁ b) (bb b) (hh b)) ∧
          (∀ b, levPt (T.Q.Xo j) yI'.1.x (x b) = (bb b ≫ (T.Q.Xo j).univ.t.act.act πE) ^ D.host.g (1 - i) * t₁ b) ∧
          ∀ I : IntData (T.Q.Xo j) T.Q.c Tc' (iT.comp io) yI'.1, ∃ S : SplitExt (Sp (IsLocalRing.ResidueField Tc'.V)),
            S.IsGt ((Over.pullback (spMap (IsLocalRing.residue Tc'.V))).obj I.G.G)

def GermIntCSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ (i : Fin 2) (πE : 𝓞 D.host.E), πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      ((D.host.g i : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI),
      Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp Tc.V)) (chD C.ch) C.xT C.eT →
      (∃ S : SplitExt (Sp (IsLocalRing.ResidueField Tc.V)),
        S.IsGt ((Over.pullback (spMap (IsLocalRing.residue Tc.V))).obj C.I.G.G)) →
      letI := io.toAlgebra
      ∀ (t₁ bb : ptO (T.Q.Xo j) yI.1.x ⟶ (T.Q.Xo j).univ.t.G)
        (hh : LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((kMix D i : ℕ) : ℤ) (ptO (T.Q.Xo j) yI.1.x))),
      IsMixedOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP ((T.Q.Xo j).univ.t.act.act πE)
        (D.host.g (1 - i)) (kMix D i) (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2)) yI.1.s t₁ bb hh →
      ∃ g : Germ.PS Tc.Fr 1 (chD C.ch),
        IsGerm yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP (kMix D i) hh g ∧ IsIntPS Tc g

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeF
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem eig_basis_of_full {x : Sp S ⟶ Xo.X} (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (hu : ∀ τ i, IsTanAt x (u τ i)) (heig : ∀ τ i, IsEigAt c τ (u τ i))
    (hfull : ∀ m : TanM x Xo.univ.t.G, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S,
      m = ∑ k, a k • tvOf (hu k.1 k.2))
    (τ : E →+* ℂ) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) (hwe : IsEigAt c τ w) :
    ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w := by
  classical
  obtain ⟨a, ha, ha_uniq⟩ := hfull (tvOf hw)
  obtain ⟨α, hα, -, -⟩ := exists_sepElt c.F.val.toRingHom (fun τ => embK c τ)
    (fun τ a => rfl)
  obtain ⟨mm, hmm_def⟩ : ∃ mm : (E →+* ℂ) → TanM x Xo.univ.t.G,
      mm = fun τ' => ∑ i, a ⟨τ', i⟩ • tvOf (hu τ' i) := ⟨_, rfl⟩
  obtain ⟨mm', hmm'_def⟩ : ∃ mm' : (E →+* ℂ) → TanM x Xo.univ.t.G,
      mm' = fun τ' => if τ' = τ then tvOf hw else 0 := ⟨_, rfl⟩
  have hmm : ∀ τ', IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ') (mm τ') := by
    intro τ'
    rw [hmm_def]
    exact eig_comb τ' (fun i => tvOf (hu τ' i))
      (fun i => (eigAt_iff (c := c) (hu τ' i) τ').1 (heig τ' i)) (fun i => a ⟨τ', i⟩)
  have hmm' : ∀ τ', IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ') (mm' τ') := by
    intro τ'
    rw [hmm'_def]
    show IsEigV _ _ (if τ' = τ then tvOf hw else 0)
    by_cases h : τ' = τ
    · rw [if_pos h, h]
      exact (eigAt_iff (c := c) hw τ).1 hwe
    · rw [if_neg h]
      show ∀ b, _ = _
      intro b
      rw [map_zero, smul_zero]
  have hsum : ∑ τ', mm τ' = tvOf hw := by
    rw [hmm_def, ha, Fintype.sum_sigma]
  have hsum' : ∑ τ', mm' τ' = tvOf hw := by
    rw [hmm'_def]
    simp
  have h1 := proj_sum_eig (ρ := actR (x0 := x) (S := S) Xo.univ.t.act) (χ := fun τ => embK c τ) (α := α)
    hα mm hmm τ
  have h2 := proj_sum_eig (ρ := actR (x0 := x) (S := S) Xo.univ.t.act) (χ := fun τ => embK c τ) (α := α)
    hα mm' hmm' τ
  rw [hsum] at h1
  rw [hsum'] at h2
  have key : tvOf hw = mm τ := by
    rw [← h1, h2, hmm'_def]
    simp
  refine ⟨fun i => a ⟨τ, i⟩, (combAt_iff (u τ) (hu τ) _ hw).2 ?_, ?_⟩
  · rw [key, hmm_def]
  · intro b hb
    rw [combAt_iff (u τ) (hu τ) b hw] at hb
    let a' : (Σ τ' : E →+* ℂ, Fin (Dw.mult τ')) → S := fun k =>
      if h : k.1 = τ then b (Fin.cast (congrArg Dw.mult h) k.2) else 0
    have ha' : tvOf hw = ∑ k, a' k • tvOf (hu k.1 k.2) := by
      rw [hb, Fintype.sum_sigma, Finset.sum_eq_single τ]
      · simp [a']
      · intro τ' _ hne
        simp [a', hne]
      · simp
    have hA := ha_uniq a' ha'
    funext i
    have hi := congrFun hA ⟨τ, i⟩
    simpa [a'] using hi

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def GamAt {D : D7} (T : Top D) : Prop :=
  ∀ (j : ℕ) (_hj : InR D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (γ : GL (Fin D.R.r) D.host.E), IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ →
    (∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y) →
    γ ∈ ((T.U j σ).X k).Γ

def ModelGamSt : Prop := ∀ (D : D7) (T : Full D), LawsFull T → GamAt T.toTop

def HalfDiffNormSt : Prop :=
  ∀ D : D7, 0 < Ideal.absNorm D.host.𝔟 ∧
    2 * Real.log (Ideal.absNorm D.host.𝔟 : ℝ) ≤ Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)|

def ShortInvSt : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j), SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L →
    ∃ (B : ℝ) (a : D.host.E), Real.log B ≤ 3 * large₂.sc.L ∧ a ≠ 0 ∧ a ∈ D.host.AA⁻¹ ∧
      ∀ τ : D.host.E →+* ℂ, ‖τ a‖ ≤ B

def ModelLatSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp,
    ∃ (L' : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (NA NC g M : ℕ),
      L'.FG ∧ (∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (herm ((T.U j σ).X k).Gm x y)) ∧
      (∀ x, (∀ y ∈ L', IsIntegral ℤ (herm ((T.U j σ).X k).Gm x y)) → x ∈ L') ∧
      ((T.U j σ).X k).Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ L', v = a • u} ∧
      0 < NA ∧ 0 < NC ∧ (∀ x ∈ ((T.U j σ).X k).Λ, (NA : D.host.E) • x ∈ L') ∧
      (∀ x ∈ L', (NC : D.host.E) • x ∈ ((T.U j σ).X k).Λ) ∧ g = T.Q.l.M ∧ 0 < g ∧
      (∀ γ : GL (Fin D.R.r) D.host.E, IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ →
        (∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
          Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (g : D.host.E) • y) →
        γ ∈ ((T.U j σ).X k).Γ) ∧
      0 < M ∧ Real.log NA ≤ D.R.f * lrd D ∧ Real.log NC ≤ 2 * large₂.sc.L ∧ Real.log M ≤ 23 * large₂.sc.L ∧
      (∃ B : ℝ, Real.log B ≤ 3 * large₂.sc.L ∧ ∀ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 →
        ∃ a : D.host.E, a ≠ 0 ∧ a • v ∈ L' ∧ ∀ τ : D.host.E →+* ℂ, ‖τ a‖ ≤ B) ∧
      (∀ v ∈ L', herm ((T.U j σ).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b →
        ∃ γ ∈ ((T.U j σ).X k).Γ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
          transvMat ((T.U j σ).X k).Gm v ((M : D.host.E) * b * ((T.U j σ).X k).κ0)) ∧
      NA = Ideal.absNorm D.host.𝔟 ∧ NC = Ideal.absNorm D.host.ccK

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section LC

variable {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X))
  (ε : K → ℤ) (H : Y' ⟶ Y)

theorem wchart_pull_le' (e : ∀ k, H ≫ φ k = φ' k) (j : K → L.ι) :
    (LB.LinComb L φ' ε).U j ≤ H ⁻¹ᵁ (LB.LinComb L φ ε).U j := by
  intro p hp
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : p ∈ (φ' k).base ⁻¹' (L.U (j k) : Set X) := Set.mem_iInter.1 hp k
  rw [← e k] at h1
  simpa using h1

theorem map_prod_pullU (e : ∀ k, H ≫ φ k = φ' k) (U : K → X.Opens) (u : ∀ k, Γ(X, U k)ˣ) (V : Y.Opens)
    (V' : Y'.Opens) (hV : ∀ k, V ≤ φ k ⁻¹ᵁ U k) (hV' : ∀ k, V' ≤ φ' k ⁻¹ᵁ U k) (hH : V' ≤ H ⁻¹ᵁ V) :
    Units.map (H.appLE V V' hH).hom.toMonoidHom (∏ k, (res (hV k) (pullU (φ k) (U k) (u k))) ^ ε k) =
      ∏ k, (res (hV' k) (pullU (φ' k) (U k) (u k))) ^ ε k := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  congr 1
  ext
  show (H.appLE V V' hH).hom (((φ k).appLE (U k) V (hV k)).hom (u k : Γ(X, U k))) =
    ((φ' k).appLE (U k) V' (hV' k)).hom (u k : Γ(X, U k))
  show ((φ k).appLE (U k) V (hV k) ≫ H.appLE V V' hH).hom (u k : Γ(X, U k)) = _
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr (e k) (U k) V' _ (hV' k)]

def pullSecF (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) (j : K → L.ι) :
    Γ(Y', (LB.LinComb L φ' ε).U j) :=
  (H.appLE ((LB.LinComb L φ ε).U j) ((LB.LinComb L φ' ε).U j) (wchart_pull_le' L φ φ' ε H e j)).hom (s.f j)

set_option maxHeartbeats 1000000 in
theorem pullSecF_compat (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) (i j : K → L.ι) :
    (Y'.presheaf.map (homOfLE (inf_le_left : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
        (LB.LinComb L φ' ε).U i)).op).hom (pullSecF L φ φ' ε H e s i) =
      ((LB.LinComb L φ' ε).g i j : Γ(Y', (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j)) *
        (Y'.presheaf.map (homOfLE (inf_le_right : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
          (LB.LinComb L φ' ε).U j)).op).hom (pullSecF L φ φ' ε H e s j) := by
  have hW : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
      H ⁻¹ᵁ ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) :=
    fun p hp => ⟨wchart_pull_le' L φ φ' ε H e i hp.1, wchart_pull_le' L φ φ' ε H e j hp.2⟩
  have hres : ∀ (k : K → L.ι) (hk : (LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U k)
      (hk' : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤ (LB.LinComb L φ' ε).U k),
      (Y'.presheaf.map (homOfLE hk').op).hom (pullSecF L φ φ' ε H e s k) =
        (H.appLE _ _ hW).hom ((Y.presheaf.map (homOfLE hk).op).hom (s.f k)) := by
    intro k hk hk'
    show (H.appLE _ _ (wchart_pull_le' L φ φ' ε H e k) ≫ Y'.presheaf.map (homOfLE hk').op).hom (s.f k) =
      (Y.presheaf.map (homOfLE hk).op ≫ H.appLE _ _ hW).hom (s.f k)
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hu : Units.map (H.appLE _ _ hW).hom.toMonoidHom ((LB.LinComb L φ ε).g i j) = (LB.LinComb L φ' ε).g i j :=
    map_prod_pullU φ φ' ε H e (fun k => L.U (i k) ⊓ L.U (j k)) (fun k => L.g (i k) (j k)) _ _
      (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)))
      (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ' i k)) (inf_le_right.trans (LB.wchart_le L φ' j k))) hW
  have hg : (H.appLE _ _ hW).hom ((LB.LinComb L φ ε).g i j : Γ(Y, (LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j)) =
      ((LB.LinComb L φ' ε).g i j : Γ(Y', (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j)) :=
    congrArg Units.val hu
  rw [hres i inf_le_left inf_le_left, hres j inf_le_right inf_le_right, ← hg, ← map_mul]
  exact congrArg (H.appLE _ _ hW).hom (s.compat i j)

def pullSecLC (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) : LB.Sec (LB.LinComb L φ' ε) where
  f := pullSecF L φ φ' ε H e s
  compat := pullSecF_compat L φ φ' ε H e s

end LC

theorem exists_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' : Over S}
    (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A) (s : LB.Sec (LPow A L a T)) :
    ∃ s' : LB.Sec (LPow A L a T'), IsPullSec A L a h hh s s' := by
  have e : ∀ _k : Fin 1, h.left ≫ (snd T A).left = (snd T' A).left := fun _ => by rw [← Over.comp_left, hh]
  exact ⟨pullSecLC L _ _ _ h.left e s, fun j => rfl⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTieAsm
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    (l.M : 𝓞 E) ∈ l.Mb := by
  have h1 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h1
  exact (Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))) h1

theorem mem_Mb_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M ^ 2 : ℕ) : 𝓞 E) ∈ l.Mb ^ 2 := by
  rw [Nat.cast_pow]
  exact Ideal.pow_mem_pow (mem_Mb l) 2

theorem act_natCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (n : ℕ) : t.act.act (n : 𝓞 E) = 𝟙 _ ^ n := by
  have act0 : t.act.act 0 = 1 := by
    have h0 := t.act.add 0 0
    rw [add_zero] at h0
    exact mul_eq_left.1 h0.symm
  induction n with
  | zero => rw [Nat.cast_zero, act0, pow_zero]
  | succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, pow_succ]

theorem pow_of_killedBy {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (u : T ⟶ Xo.univ.t.G) (h : KilledBy Xo (l.Mb ^ 2) u) :
    u ^ (l.M ^ 2) = 1 := by
  have e := h _ (mem_Mb_sq l)
  rw [act_natCast, MonObj.comp_pow, Category.comp_id] at e
  exact e

theorem regTie_of (hU : UnifAtIntLaSt) (hR : RegUnifSt) (hV : VtMoveSt) (hT : ThetaTieSt) : RegTieSt := by
  intro D T h j hj _ _ Tc io yI e la ho hy hM I hsplit x F hVt
  let _ := io.toAlgebra
  obtain ⟨P, hP⟩ := hU D T h j hj Tc io yI e la ho hy hM I hsplit
  obtain ⟨θ, hθ, θK, hθ1, hθ2⟩ := hT _ _ _ _ _ _ Tc io yI.1 I
  obtain ⟨ttK, FK, hVK, hFK⟩ := hV _ _ _ _ _ yI.1.x I.t' I.m1 I.w1 I.rig1 T.Q.l.M _ yI.1.s _ F hVt
    (fun u hu => pow_of_killedBy _ u hu) θK hθ1
  obtain ⟨σ, hσ⟩ := hR _ _ Tc.V I.G P hP θ hθ T.Q.l.M (isUnit_natCast_of_overLa Tc ho hM) I.t' I.m2 I.w2 I.rig2
    θK hθ2 ttK FK hVK
  obtain ⟨σt, hσt⟩ := exists_restrict I.t' _ (zCast I.t'.G (natCast_sq T.Q.l.M) FK)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left),
      (r ≫ gsec I.t'.G) ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left = r := fun r => by
    rw [Category.assoc, gsec_snd, Category.comp_id]
  refine ⟨σ, σt, fun Z r zp h1 h2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [hσt Z r z J' hJ']
    exact hFK Z r zp (r ≫ gsec I.t'.G) h1 h2 (hg r) z J J' hJ hJ'
  · rw [hσt Z r z J' hJ']
    exact hσ Z r (r ≫ gsec I.t'.G) (hg r) z J J' hJ hJ'

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

