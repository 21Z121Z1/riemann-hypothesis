import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.LongGeneratorWeights
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0166
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.CMObjBundlePull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0046
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0036
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0058
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0037
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0052
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0107
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjCmHostRootNeSelf
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeafCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.LongGeneratorWeights

variable {D : D7}

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h5
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
  have h6 := H.sqrt_neg_disc_sq
  rw [hx] at h6
  have h7 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast h6
  have h8 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg x]

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauEmb_ne_conj (Q : Par D) (hp : Q.PinHost) (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 := hp.2.2.2 t
  rw [h] at h1
  have h2 : (starRingEnd ℂ) (DV.tauEmb D t' (Q.H.rt : D.host.E)) = Q.H.rt0 := h1
  rw [hp.2.2.2 t'] at h2
  exact conj_cmHostRoot_ne_self Q.H h2

theorem exists_tau (Q : Par D) (hp : Q.PinHost) (τ : D.host.E →+* ℂ) (hτ : InPsi Q.H τ) :
    ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
  by_cases hgP : g ∈ D.R.Psi
  · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
    exact ⟨t, hg.symm.trans ht⟩
  · exfalso
    have h2 : g * D.R.cc ∈ D.R.Psi := by
      by_contra h
      exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
    obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
    have h3 : DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0 := hp.2.2.2 t
    rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
    have h4 : τ (D.host.conj (Q.H.rt : D.host.E)) = star (τ (Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
    have hτ' : τ (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    apply conj_cmHostRoot_ne_self Q.H
    calc star Q.H.rt0 = star (τ (Q.H.rt : D.host.E)) := by rw [hτ']
      _ = τ (D.host.conj (Q.H.rt : D.host.E)) := h4.symm
      _ = Q.H.rt0 := h3

theorem wtA_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj Q hp]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj Q hp, this]
  · simp

def NoBaseRows (T : Top D) : Prop :=
  ∀ (large₂ : SizeData₂ D) (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, ThetaWt D w →
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → WeightAlgebra.DF w + 2 ≤ qq D → T.Q.l.Mb.IsPrincipal →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp,
      ∃ f ∈ T.C j w,
        (∃ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
          (P ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA w) w.n ∧
            ∀ σ' : T.Q.c.F →+* ℂ, l1At σ' P ≤ Real.exp (140 * D.R.r * large₂.sc.L * WeightAlgebra.DF w)) ∧
          IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f) ∧ NeZeroOn T j σ k f

theorem wt_ext {j : ℕ} {w w' : WeightFamilies.Wt D j} (h1 : w.aP = w'.aP) (h2 : w.aM = w'.aM) (h3 : w.n = w'.n) : w = w' := by
  cases w; cases w'; simp_all

def WeightsExist : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (j : ℕ) (hj : InR D j)
    (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    Formalism.MainNotions.Gaps.FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 →
    (∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2) ∧ (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW)

theorem anti_nonneg {p : ℕ} (g : Fin p → ℤ) (h1 : ∀ (i : Fin p) (h : i.1 + 1 < p), g ⟨i.1 + 1, h⟩ ≤ g i)
    (h2 : ∀ i : Fin p, i.1 + 1 = p → 0 ≤ g i) : Antitone g ∧ ∀ i, 0 ≤ g i := by
  cases p with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n =>
    have ha : Antitone g := Fin.antitone_iff_succ_le.2 fun i => h1 i.castSucc (by simp)
    exact ⟨ha, fun i => (h2 (Fin.last n) rfl).trans (ha (Fin.le_last i))⟩

theorem div_step (a c q T' : ℤ) (hp : 0 < T') (hc : c ≤ T') (ha : T' * T' ≤ a - c)
    (hq : q = Int.fdiv (a - c) T') : a ≤ (T' + 2) * q := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le] at hq
  have h1 : a - c < (q + 1) * T' := by rw [hq]; exact Int.lt_ediv_add_one_mul_self _ hp
  have h2 : T' ≤ q := by
    by_contra hlt
    have h3 : q + 1 ≤ T' := by omega
    nlinarith [mul_le_mul_of_nonneg_right h3 hp.le]
  nlinarith

theorem block {p : ℕ} (a l : Fin p → ℕ) (Dm T r c : ℕ) (h40 : 40 * (Dm + 2) ≤ T) (hc : c ≤ T)
    (hgap : ∀ i : Fin p, i.1 + 1 < p → (((T + Dm + 2) * ((T + Dm + 2) + 2 * r) : ℕ) : ℤ) ≤ gapZ a i + 2)
    (hlast : ∀ i : Fin p, i.1 + 1 = p → 2 * T ^ 2 ≤ a i)
    (hL : ∀ i, gapZ l i = if i.1 + 1 < p then Int.fdiv (gapZ a i - (-2)) ((T + Dm + 2 : ℕ) : ℤ)
      else Int.fdiv ((a i : ℤ) - c) ((T + Dm + 2 : ℕ) : ℤ)) :
    Antitone (fun i => ((T : ℤ) + Dm + 4) * l i - a i) ∧ ∀ i, 0 ≤ ((T : ℤ) + Dm + 4) * l i - a i := by
  refine anti_nonneg _ (fun i h => ?_) (fun i h => ?_)
  · have e := hL i
    rw [if_pos h] at e
    have hg := hgap i h
    have := div_step (gapZ a i) (-2) (gapZ l i) ((T + Dm + 2 : ℕ) : ℤ) (by positivity) (by omega)
      (by push_cast at hg ⊢; nlinarith [mul_nonneg (by positivity : (0 : ℤ) ≤ T + Dm + 2) (by positivity : (0 : ℤ) ≤ r)]) e
    simp only [gapZ, dif_pos h] at this
    push_cast at this
    nlinarith
  · have hn : ¬ i.1 + 1 < p := by omega
    have e := hL i
    rw [if_neg hn] at e
    simp only [gapZ, dif_neg hn] at e
    have hl : 2 * (T : ℤ) ^ 2 ≤ a i := by exact_mod_cast hlast i h
    have h40' : 40 * ((Dm : ℤ) + 2) ≤ T := by exact_mod_cast h40
    have hc' : (c : ℤ) ≤ T := by exact_mod_cast hc
    have hD : (0 : ℤ) ≤ Dm := by positivity
    have hT0 : (0 : ℤ) ≤ T := by positivity
    have := div_step (a i) c (l i) ((T + Dm + 2 : ℕ) : ℤ) (by positivity) (by omega)
      (by push_cast
          nlinarith [mul_nonneg hT0 (sub_nonneg.2 h40'), mul_nonneg (by omega : (0 : ℤ) ≤ Dm + 2) (sub_nonneg.2 h40'),
            mul_nonneg hT0 (by omega : (0 : ℤ) ≤ T - 80)]) e
    push_cast at this
    linarith

end GlobalTheory.LeafCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DimEqOfFiniteSurjective
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.LamCM Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTan
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull

namespace GlobalTheory.CMClaims

theorem laws : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
theorem secTwist : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
theorem homExt : CM.HomExtDvr := fun T K _ _ _ _ _ _ G G' _ _ hG hG' φ hφ =>
  GlobalTheory.existsUnique_hom_extension_semiAbelian T K G G' hG hG' φ hφ

section Vec

variable {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {G : Over (Sp R)} {G' : Over (Sp R')} [GrpObj G]
  [GrpObj G'] {φ : G'.left ⟶ G.left}

def push (h : IsGrpPullback G' G (spMap f) φ) (w : epsR R' ⟶ G') : epsAt (spMap f) ⟶ G :=
  Over.homMk (w.left ≫ φ) (by
    change (w.left ≫ φ) ≫ G.hom = (epsR R').hom ≫ spMap f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w w])

variable (h : IsGrpPullback G' G (spMap f) φ)

variable [IsCommMonObj G'] {n : ℕ} {v : Fin n → (epsR R' ⟶ G')} (hv : IsLieBasis v)

def comb (c : Fin n → R') : epsR R' ⟶ G' := ((LieComb.lieComb_algebra R' G' n v hv.1).1 c).exists.choose

theorem isLieComb_iff (c : Fin n → R') (w : epsR R' ⟶ G') : IsLieComb c v w ↔ w = comb hv c :=
  have a := ((LieComb.lieComb_algebra R' G' n v hv.1).1 c).exists.choose_spec
  ⟨fun b => ((LieComb.lieComb_algebra R' G' n v hv.1).1 c).unique b a, fun b => b ▸ a⟩

theorem isLieComb_comb (c : Fin n → R') : IsLieComb c v (comb hv c) := (isLieComb_iff hv c _).2 rfl

theorem isTangent_iff (w : epsR R' ⟶ G') : IsTangent w ↔ ∃ c, comb hv c = w :=
  ⟨fun a => (hv.2 w a).exists.imp fun c b => ((isLieComb_iff hv c w).1 b).symm,
    fun ⟨c, a⟩ => a ▸ (LieComb.lieComb_algebra R' G' n v hv.1).2.1 _ _ (isLieComb_comb hv c)⟩

theorem comb_injective : Function.Injective (comb hv) := fun a b e =>
  (hv.2 _ ((isTangent_iff hv _).2 ⟨a, rfl⟩)).unique (isLieComb_comb hv a) (e ▸ isLieComb_comb hv b)

def vecOf (c : Fin n → R') : epsAt (spMap f) ⟶ G := push h (comb hv c)

end Vec

section Pair

variable {K : Type} [Field K] [NumberField K]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E}

end Pair

section Isog

theorem card_torsion_eq {M N : Type} [CommGroup M] [CommGroup N] (F : M →* N) (hF : Function.Surjective F) (m : ℕ)
    (hm : ∀ x, F x = 1 → x ^ (m + 1) = 1) :
    Nat.card {x : M // x ^ (m + 2) = 1} = Nat.card {y : N // y ^ (m + 2) = 1} := by
  refine Nat.card_eq_of_bijective (fun x => ⟨F x.1, by rw [← map_pow, x.2, map_one]⟩) ⟨fun a b e => ?_, fun y => ?_⟩
  · have e₁ : F (a.1 / b.1) = 1 := by rw [map_div, div_eq_one]; exact congrArg Subtype.val e
    have e₂ : (a.1 / b.1) ^ (m + 2) = 1 := by rw [div_pow, a.2, b.2, div_one]
    rw [pow_succ, hm _ e₁, _root_.one_mul, div_eq_one] at e₂
    exact Subtype.ext e₂
  · obtain ⟨x, hx⟩ := hF y.1
    have e₁ : (x ^ (m + 2)) ^ (m + 1) = 1 := hm _ (by rw [map_pow, hx, y.2])
    refine ⟨⟨x ^ ((m + 1) * (m + 1)), ?_⟩, Subtype.ext ?_⟩
    · rw [← pow_mul, show (m + 1) * (m + 1) * (m + 2) = (m + 2) * (m + 1) * (m + 1) by ring, pow_mul, pow_mul, e₁, one_pow]
    · change F _ = y.1
      rw [map_pow, hx, show (m + 1) * (m + 1) = (m + 2) * m + 1 by ring, pow_succ, pow_mul, y.2, one_pow, _root_.one_mul]

variable {K : Type} [Field K] [NumberField K]

theorem onto_points {R k : Type} [CommRing R] [Field k] [IsAlgClosed k] {P Q : Over (Sp R)} (Φ : P ⟶ Q)
    [IsFinite Φ.left] [Surjective Φ.left] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ Q) : ∃ x : Over.mk t ⟶ P, y = x ≫ Φ := by
  obtain ⟨p, hp⟩ := GeomSurj.exists_lift_of_surjective Φ.left y.left
  refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp⟩
  rw [← Over.w Φ, ← Category.assoc, ← hp]
  exact Over.w y

end Isog

section Sum

variable {K : Type} [Field K] [NumberField K]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l} {p q : ℕ}

end Sum

section Types

variable {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φ : x.P.A.left ⟶ A.A.left}

def vec (hf : abelian₂.IsFibreOf A x (abelian₂.gmap K) φ) (i : Fin x.P.g) : epsAt (genPt K) ⟶ A.A := push hf.1 (x.v i)

variable {E : Type} [Field E] [NumberField E]

def resLab (lab : (E →+* ℂ) → (E →+* K)) (t : E →+* ℂ) : 𝓞 E →+* K := (lab t).comp (algebraMap (𝓞 E) E)

end Types

section Lines

variable {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φ : x.P.A.left ⟶ A.A.left}

end Lines

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def conjType (H : Host E) : {τ : E →+* ℂ // τ (H.rt : E) ≠ H.rt0} ≃ psiBar H :=
  Equiv.subtypeEquivRight (LamF.host_mem_compl_psiSet H)

variable [StarRing (𝓞 E)] {l : Level H} {c : Coeff l} {p q : ℕ}

def Readable (o : abelian₂.LamObj c p q) : Prop :=
  abelian₂.IsFibreOf o.AΨ o.xΨ (abelian₂.gmap o.K₁) o.φΨg ∧ abelian₂.IsFibreOf o.A' o.x' (abelian₂.gmap o.K₁) o.φ'g ∧
    (∀ i, IsMonHom (o.φΨ i)) ∧ (∀ i, IsMonHom (o.φ' i)) ∧
    (∀ i (a : 𝓞 E), o.oaΨ.act a ≫ o.φΨ i = o.φΨ i ≫ o.oa.act a) ∧
    ∀ i (a : 𝓞 E), o.oa'.act a ≫ o.φ' i = o.φ' i ≫ o.oa.act a

theorem Readable.fibP {o : abelian₂.LamObj c p q} (h : Readable o) : abelian₂.IsFibreOf o.AΨ o.xΨ (abelian₂.gmap o.K₁) o.φΨg := h.1
theorem Readable.fibC {o : abelian₂.LamObj c p q} (h : Readable o) : abelian₂.IsFibreOf o.A' o.x' (abelian₂.gmap o.K₁) o.φ'g := h.2.1
theorem Readable.homP {o : abelian₂.LamObj c p q} (h : Readable o) (i : Fin p) : IsMonHom (o.φΨ i) := h.2.2.1 i
theorem Readable.homC {o : abelian₂.LamObj c p q} (h : Readable o) (i : Fin q) : IsMonHom (o.φ' i) := h.2.2.2.1 i
theorem Readable.linP {o : abelian₂.LamObj c p q} (h : Readable o) (i : Fin p) (a : 𝓞 E) :
    o.oaΨ.act a ≫ o.φΨ i = o.φΨ i ≫ o.oa.act a := h.2.2.2.2.1 i a
theorem Readable.linC {o : abelian₂.LamObj c p q} (h : Readable o) (i : Fin q) (a : 𝓞 E) :
    o.oa'.act a ≫ o.φ' i = o.φ' i ≫ o.oa.act a := h.2.2.2.2.2 i a

def TargetLines (o : abelian₂.LamObj c p q) : Prop :=
  abelian₂.IsFibreOf o.B o.xB (abelian₂.gmap o.K₁) o.φB ∧ o.Tl.Good ∧ o.LamL.Good ∧ (∀ v, KeyLocAt o.xB o.Tl o.LamL v) ∧
    (∀ σ, KeyArchAt o.xB o.Tl o.LamL σ) ∧ ∀ v, ∃ M, abelian₂.IsModelAt o.B o.xB o.φB v M ∧ IsLocGen v M.det o.LamL.I

def toCM (o : abelian₂.LamObj c p q) (h : Readable o) : CMObj c p q where
  K := o.K₁
  B := o.B
  AP := o.AΨ
  AC := o.A'
  ιB := o.oa.toRingAct
  ιP := o.oaΨ.toRingAct
  ιC := o.oa'.toRingAct
  φP := o.φΨ
  φP_hom := h.homP
  φP_lin := h.linP
  φC := o.φ'
  φC_hom := h.homC
  φC_lin := h.linC
  hP := o.hΨ
  hC := o.h'
  ηP t := vec h.fibP (o.τΨ.symm t)
  ηC t := vec h.fibC ((o.τ'.trans (conjType H)).symm t)
  ℓP t := o.ℓΨ (o.τΨ.symm t)
  ℓC t := o.ℓ' ((o.τ'.trans (conjType H)).symm t)

variable (hs : ∀ a : 𝓞 E, star a = H.bar a) (o : abelian₂.LamObj c p q) (h : Readable o)

end Main

end GlobalTheory.CMClaims
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DvdOfPullEqZero
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.BoxFrame

open GlobalTheory.IntegralBox

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem dvd_iff (D : DegPre V) {k : ℕ} {α : D.X} (a : V) (σ τ : SecMod D k α) :
    (∀ j, LB.Sec.f σ j = constFn D.P.A.hom _ a * LB.Sec.f τ j) ↔ σ = a • τ :=
  ⟨fun h => SecOps.sec_ext h, fun h j => congrArg (fun s : SecMod D k α => LB.Sec.f s j) h⟩

theorem dvd_of_pull_eq_zero (hT : TwistBaseChangeStatement) {ϖ : V} (hϖ : Irreducible ϖ) (D : DegPre V) {k : ℕ}
    (hk : 1 ≤ k) {α : D.X} (σ : SecMod D k α) (h : pullBC (residue V) D k α σ = 0) :
    ∃ τ : SecMod D k α, σ = ϖ • τ := by
  obtain ⟨b, hb, hb'⟩ := exists_basis (residue V) D hT hk α
  obtain ⟨c, rfl⟩ := hb σ
  have h0 := hb' (fun i => residue V (c i)) (by simpa only [map_sum, map_smulₛₗ] using h)
  have hd : ∀ i, ϖ ∣ c i := fun i => by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]
    exact congrFun h0 i
  choose d hd using hd
  exact ⟨∑ i, d i • b i, by simp only [hd, Finset.smul_sum, smul_smul]⟩

theorem exists_pull_ne_zero (hT : TwistBaseChangeStatement) (D : DegPre V) (α : D.X) :
    ∃ σ : SecMod D 1 α, pullBC (residue V) D 1 α σ ≠ 0 := by
  classical
  obtain ⟨b, -, hb'⟩ := exists_basis (residue V) D hT le_rfl α
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  refine ⟨b i₀, fun h => ?_⟩
  have h0 := hb' (Pi.single i₀ 1) (by
    rw [Finset.sum_eq_single i₀, h, smul_zero]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h)
  simpa using congrFun h0 i₀

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (n : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre n) (F : Type) [Field F] [Algebra (FractionRing V) F] (θ : Fam D.toPre F 1) (Θ : Fam D'.toPre F 1), ThFrame D ϖ F θ → IsBoxFam pD F 1 Θ (fun _ => θ) → ThFrame D' ϖ F Θ := by
  intro V _ _ _ _ ϖ hϖ n D D' pD F _ _ θ Θ ⟨σ, σF, hs, he, hn⟩ hB
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  have hex : ∀ α : D.toPre.X, ∃ s : SecMod D.toPre 1 α, pullBC (residue V) D.toPre 1 α s ≠ 0 ∧
      (α = 0 → GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε 1) (θ.s α)
        (D.toPre.famφB α) (DegPre.famε 1) s (DegPre.prB D.toPre F).left 1) := fun α => by
    by_cases hα : α = 0
    · subst hα
      refine ⟨σ, fun h => ?_, fun _ => ?_⟩
      · obtain ⟨τ, hτ⟩ := dvd_of_pull_eq_zero hT hϖ D.toPre le_rfl σ h
        exact hn ⟨τ, (dvd_iff D.toPre ϖ σ τ).2 hτ⟩
      · rw [show θ.s 0 = σF from SecOps.sec_ext he]
        exact hs
    · obtain ⟨s, hs⟩ := exists_pull_ne_zero hT D.toPre α
      exact ⟨s, hs, fun h => absurd h hα⟩
  choose f hf hf' using hex
  refine ⟨boxFamB pD 1 (fun _ α => f α) 0, Θ.s 0,
    UnitBallBox.box_secScal pD hB (isBoxFamB_boxFamB pD 1 _) 0
      (fun i => hf' _ (by rw [map_zero]; rfl)), fun _ => rfl, ?_⟩
  rintro ⟨τ, hτ⟩
  have h1 := (dvd_iff D'.toPre ϖ _ τ).1 hτ
  have h2 : residue V ϖ = 0 := (residue_eq_zero_iff _).2 (by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
  have h3 : pullBC (residue V) D'.toPre 1 0 (boxFamB pD 1 (fun _ α => f α) 0) = 0 := by
    exact (congrArg _ h1).trans ((map_smulₛₗ (pullBC (residue V) D'.toPre 1 0) ϖ τ).trans (by rw [h2, zero_smul]))
  have h4 := box_indep (residue V) pD (m := 1) (fun α _ => f α) (fun α c hc => by
    rw [Fin.sum_univ_one, smul_eq_zero] at hc
    funext i
    rw [Subsingleton.elim i 0]
    exact hc.resolve_right (hf α)) 0 (fun _ => 1) (Finset.sum_eq_zero fun a _ => (congrArg _ h3).trans (smul_zero _))
  exact one_ne_zero (congrFun h4 fun _ => 0)

end GlobalTheory.BoxFrame
end

