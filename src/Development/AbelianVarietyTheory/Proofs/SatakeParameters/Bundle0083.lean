import Mathlib
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0382
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeValuationBound
section
noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

namespace GlobalTheory.Proof.LatticeValuationBound

section Chain

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}

def StepCmp (M : MemberForms LL embLL Pl Tau hc C A P) {p : ℕ} {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl}
    (Ch : Chain Lv) (σ : LL →+* G.Kf) (start : (M.lat 0).V → Lv.Fm 0) : Prop :=
  ∃ cmp : ∀ j, (M.lat j).V →ₛₗ[σ] Lv.Fm j,
    (∀ x, cmp 0 x = start x) ∧
    (∀ j, j < R.m → ∀ (x : (M.lat j).V) (y : (M.lat (j + 1)).V),
      M.emb (j + 1) y = C.K j (M.emb j x) → cmp (j + 1) y = Ch.Kz j (cmp j x)) ∧
    (LinearIndependent G.Kf fun a => cmp R.m ((M.lat R.m).b a)) ∧
    Lv.Int R.m ≤ Submodule.span G.O (cmp R.m '' ((M.lat R.m).L : Set (M.lat R.m).V))

theorem exists_chain (M : MemberForms LL embLL Pl Tau hc C A P) {p : ℕ} {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl}
    (Ch : Chain Lv) (σ : LL →+* G.Kf) (cmp : ∀ j, (M.lat j).V →ₛₗ[σ] Lv.Fm j)
    (hK : ∀ j, j < R.m → ∀ (x : (M.lat j).V) (y : (M.lat (j + 1)).V),
      M.emb (j + 1) y = C.K j (M.emb j x) → cmp (j + 1) y = Ch.Kz j (cmp j x))
    (hrat : ∀ j, j < R.m → M.KRat j) (x : (M.lat 0).V) (j : ℕ) (hj : j ≤ R.m) :
    ∃ y : (M.lat j).V, M.emb j y = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap j (M.emb 0 x) ∧ cmp j y = Ch.chainK j (cmp 0 x) := by
  induction j with
  | zero => exact ⟨x, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨y, hy, hy'⟩ := ih (by omega)
    obtain ⟨z, hz⟩ := hrat j (by omega) y
    refine ⟨z, ?_, ?_⟩
    · rw [hz, hy]; rfl
    · rw [hK j (by omega) y z hz, hy']; rfl

end Chain

variable {D : D7}

def CmpRef (c : LatCmp D) (Dx : DivX D) {Y : LatInst D} (W : TwLoc D Y) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.places.resChar w ∉ Dx.Qp D.what₂.mu0 →
    StepCmp (D.fm u) (W.LC D.what₂.mu0 u w hg).2 (c.embW u w hg) (fun x => c.cmp u w hg x)

def CmpTwAt (c : LatCmp D) (T : TwForms D) {Y : LatInst D} (W : TwLoc D Y) (μ : D.what₂.Tup) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Prop :=
  StepCmp (T.fm u μ) (W.LC μ u w hg).2 (c.embW u w hg) (fun x => c.cmp u w hg ((T.e0 u μ).symm x))

def CmpTw (c : LatCmp D) (Dx : DivX D) (T : TwForms D) {Y : LatInst D} (W : TwLoc D Y) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) μ,
    DV.Used D μ → μ ≠ D.what₂.mu0 → D.what₂.places.resChar w ∉ Dx.Qp μ → CmpTwAt c T W μ u w hg

def RatRef (D : D7) : Prop := ∀ u, ∀ i < D.R.m, (D.fm u).KRat i

def RatTw (T : TwForms D) : Prop :=
  ∀ u μ, DV.Used D μ → μ ≠ D.what₂.mu0 → ∀ i < D.R.m, (T.fm u μ).KRat i

def StepZeroRef (D : D7) : Prop := ∀ u φ, HEq (D.e0Tw u D.what₂.mu0 φ) φ

theorem col_heq {R : Ranks} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc}
    (h : C = C') {φ : C.cls 0 → C.Y 0 → ℂ} {φ' : C'.cls 0 → C'.Y 0 → ℂ} (hφ : HEq φ φ') :
    HEq (C.col φ) (C'.col φ') := by
  subst h
  rw [eq_of_heq hφ]

theorem VGe_symm {w : D.what₂.places.Pl} (A B : HLat D.what₂.LL) (e : A.V ≃ₗ[D.what₂.LL] B.V)
    (he : ∀ x, x ∈ A.L ↔ e x ∈ B.L) {y : B.V} {s : ℝ} (h : VGe D w B.L y s) : VGe D w A.L (e.symm y) s := by
  obtain ⟨a, z, hz, rfl, ha⟩ := h
  refine ⟨a, e.symm z, ?_, map_smul _ _ _, ha⟩
  obtain ⟨t, ht, hz⟩ := (D.mem_locW_iff w _ _).1 hz
  refine (D.mem_locW_iff w _ _).2 ⟨t, ht, (he _).2 ?_⟩
  rw [← algebraMap_smul D.what₂.LL t, map_smul, LinearEquiv.apply_symm_apply, algebraMap_smul]
  exact hz

theorem colGe0_of_colGeTw (T : TwForms D) (h0 : StepZeroRef D) {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {x : ((D.fm u).lat 0).V} {s : ℝ} (h : ColGeTw T u D.what₂.mu0 w x s) : ColGe0 D u w x s := by
  obtain ⟨y, hy, hv⟩ := h
  refine ⟨(T.eMu0 u D.R.m le_rfl).symm y, ?_, VGe_symm _ _ _ (T.eMu0_lat u D.R.m le_rfl) hv⟩
  have h1 := T.eMu0_emb u D.R.m le_rfl ((T.eMu0 u D.R.m le_rfl).symm y)
  rw [LinearEquiv.apply_symm_apply, hy] at h1
  exact eq_of_heq (h1.symm.trans (col_heq (D.memberColumns_twistedChain_base u) (h0 u _)))

def CmpTwAll (c : LatCmp D) (Dx : DivX D) (T : TwForms D) {Y : LatInst D} (W : TwLoc D Y) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) μ,
    DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → CmpTwAt c T W μ u w hg

def RatTwAll (T : TwForms D) : Prop := ∀ u μ, DV.Used D μ → ∀ i < D.R.m, (T.fm u μ).KRat i

end GlobalTheory.Proof.LatticeValuationBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemPrimeOf
section
open NumberField Filter Topology

noncomputable section

namespace GlobalTheory.Proof.IdempotentLatticeSequence

theorem mem_int_iff {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  show x ∈ (PadicComplex.valued p).v.valuationSubring ↔ _
  rw [Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def,
    ← map_one (PadicComplex.valued p).v, ← Valuation.restrict_le_iff]
  simpa only [map_one, NNReal.coe_le_one] using
    ((Valuation.RankOne.strictMono (PadicComplex.valued p).v).le_iff_le (b := 1)).symm

theorem norm_int_le {p : ℕ} [Fact p.Prime] {M : Type} [Field M] (φ : M →+* ℂ_[p]) (a : 𝓞 M) : ‖φ (a : M)‖ ≤ 1 := by
  obtain ⟨P, hmon, hev⟩ := RingOfIntegers.isIntegral_coe a
  have key : ∀ f : ℤ →+* ℂ_[p], Polynomial.eval₂ f (φ (a : M)) P = 0 := fun f => by
    rw [RingHom.ext_int f (φ.comp (algebraMap ℤ M)), ← Polynomial.hom_eval₂, hev, map_zero]
  exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral ⟨P, hmon, key _⟩

theorem flat_system {A B : Type} [CommRing A] [AddCommGroup B] [Module A B] [Module.Flat A B] {κ J : Type}
    [Fintype κ] [Fintype J] (b : κ → J → A) (r : κ → B) (h : ∀ j, ∑ k, b k j • r k = 0) :
    ∃ (n : ℕ) (a : κ → Fin n → A) (y : Fin n → B), (∀ k, r k = ∑ l, a k l • y l) ∧ ∀ l j, ∑ k, b k j * a k l = 0 := by
  classical
  let f : (J → A) →ₗ[A] (κ → A) := Matrix.mulVecLin (Matrix.of fun k j => b k j)
  let x : (κ → A) →ₗ[A] B := Fintype.linearCombination A r
  have hxf : x ∘ₗ f = 0 := by
    refine LinearMap.ext fun c => ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, x, f, Fintype.linearCombination_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp_rw [mul_comm (b _ j) (c j), mul_smul]
    rw [← Finset.smul_sum, h j, smul_zero]
  obtain ⟨n, a', y', hxa, haf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  refine ⟨n, fun k l => a' (Pi.single k 1) l, fun l => y' (Finsupp.single l 1), fun k => ?_, fun l j => ?_⟩
  · have hr : r k = x (Pi.single k 1) := by
      simp [x, Fintype.linearCombination_apply, Pi.single_apply]
    rw [hr, hxa, LinearMap.comp_apply]
    conv_lhs => rw [← Finsupp.univ_sum_single (a' (Pi.single k 1))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finsupp.smul_single_one, map_smul]
  · have h1 := congrArg (fun v => v l) (LinearMap.congr_fun haf (Pi.single j 1))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
    have hf : f (Pi.single j 1) = ∑ k, b k j • Pi.single k 1 := by
      ext k'
      simp [f, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    rw [hf, map_sum] at h1
    simpa [Finsupp.finsetSum_apply, map_smul] using h1

def primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) : Ideal (𝓞 E) where
  carrier := {a | ‖φ (a : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    change ‖φ (algebraMap (𝓞 E) E (a + b))‖ < 1
    rw [map_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  smul_mem' := fun c a ha => by
    change ‖φ (algebraMap (𝓞 E) E (c * a))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le φ c)).trans_lt ha

theorem mem_primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) (a : 𝓞 E) :
    a ∈ primeOf φ ↔ ‖φ (algebraMap (𝓞 E) E a)‖ < 1 := by
  exact Iff.rfl

theorem natCast_mem_primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) :
    (p : 𝓞 E) ∈ primeOf φ := by
  rw [mem_primeOf]
  have h1 : ‖((p : ℚ_[p]) : ℂ_[p])‖ < 1 := by
    rw [PadicComplex.norm_extends', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  simpa using h1

theorem primeOf_isPrime {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) : (primeOf φ).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ne, Ideal.eq_top_iff_one, mem_primeOf]
    simp
  · rw [mem_primeOf, map_mul, map_mul, norm_mul] at hab
    rw [mem_primeOf, mem_primeOf]
    have ha : ‖φ (algebraMap (𝓞 E) E a)‖ ≤ 1 := norm_int_le φ a
    have hb : ‖φ (algebraMap (𝓞 E) E b)‖ ≤ 1 := norm_int_le φ b
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    nlinarith [h.1, h.2, norm_nonneg (φ (algebraMap (𝓞 E) E a))]

theorem primeOf_isMaximal {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ_[p]) :
    (primeOf φ).IsMaximal := by
  refine (primeOf_isPrime φ).isMaximal ?_
  intro h
  have hp := natCast_mem_primeOf φ
  rw [h, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp

end GlobalTheory.Proof.IdempotentLatticeSequence
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem bridge_field_le_unramified : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E))
    (hw : w ∈ placesOver H.E (N.l i)),
    N.l i ∉ H.small → N.l i ≠ H.q → N.l i ≠ H.d → (nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (N.l i) := by
  intro R H what₂ N nbr i w hw h2 hq hd
  have hK := GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' (N.l i) H.E ((nbr i w hw).j.comp (algebraMap H.E N.Om)) (nbr i w hw).Kw.1
    (nbr i w hw).j_E (nbr i w hw).Kw.2 (nbr i w hw).j_dense
  rw [hK, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  exact GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified H (N.l i) h2 hq hd _ x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ProdRootsOfMonic
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne

namespace GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def WDOfTie (T : WDTie N A) : Prop :=
  ∀ (i : N.Loc) (a : ℕ) (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (w : PlE H)
    (hl : ((N.l i : ℕ) : 𝓞 H.E) ∉ w.asIdeal),
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) :
      Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
    T.e w (A.wdOf i r w) = wdOf (N.plOm.2 w) hl (A.iotaQC i) r

theorem prod_roots_of_monic {p : ℂ[X]} (hp : p.Monic) : (p.roots.map fun α => X - C α).prod = p :=
  ((IsAlgClosed.splits p).eq_prod_roots_of_monic hp).symm

theorem eigAway_of_wdOfTie : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (T : WDTie N A), WDOfTie T → GlobalTheory.LocalInv.EigAway N A T.eig := by
  intro R H what₂ N A T hT i a ρ hρ w hw σ hσ
  have hW : σ ∈ Weil (N.plOm.2 w) := mem_Weil_of_isFrob _ hσ
  have hr : Continuous (fun g => ((mapRep (iotaOQ N A i) ρ g : GL (Fin a) (Qbar (N.l i))) :
      Matrix (Fin a) (Fin a) (Qbar (N.l i)))) :=
    Continuous.matrix_map hρ (GlobalTheory.CoeffEmbedding.continuous_iotaOQ R H what₂ N A i)
  have hcomp : iotaO N A i = (A.iotaQC i).toRingHom.comp (iotaOQ N A i) := rfl
  rw [WDTie.eig, GlobalTheory.LocalInv.wd, hT i a _ w hw hr, WD.inePol_of_mem _ hW,
    prod_roots_of_monic (WD.charPol_monic _ _), charPol_wdOf hw (A.iotaQC i) hr ⟨σ, hW⟩, hcomp,
    ← Polynomial.map_map, ← Matrix.charpoly_map]
  rfl

end GlobalTheory.RowTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReductionTrivialOnWildInertia
section
noncomputable section

namespace GlobalTheory.RowWildTame

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem main : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → GlobalTheory.RowTie.LabTame D.nd D.naut → GlobalTheory.RowTie.RowRepAtG D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.ntypes.rbar σ (D.nd.w i) s = 1 := by
  intro D hT hL hR σ k v i hl hocc hgood s hs hwild
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨Sig, ρ, hP, hρ, hc⟩ := hR i σ hocc hgood
  have hw := GlobalTheory.TameLabels.not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  obtain ⟨hιc, hιi⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  have hcont : Continuous (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin D.R.r) (Qbar (D.nd.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i)))) := hρ.1.matrix_map hιc
  have e := hc k v hl
  have hdim : D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) = D.R.r := by
    have := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v)
    rw [e, D.naut.lpDim_tw] at this
    exact this
  have hfull : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locW i σ (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) := by
    rw [← D.naut.lab_loc i k σ v, (D.nd.lab_monic k σ v).2, hdim]
  have h1 := hL k v _ hfull s hs hwild
  rw [hdim] at h1
  have h2 := D.naut.wdOf_ine i (mapRep (iotaOQ D.nd D.naut i) ρ) _ hw hcont s hs
  rw [e, D.naut.inePol_tw _ _ _ hs, h1] at h2
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have h3 : ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective (iotaO D.nd D.naut i)
      ((D.naut.iotaQC i).injective.comp hιi)
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, hcomp,
      ← Polynomial.map_map, ← Matrix.charpoly_map]
    exact h2
  have h4 := hT.2 i σ hocc hgood Sig ρ hP hρ s
  rw [h3, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one] at h4
  have h5 : ((D.ntypes.rbar σ (D.nd.w i) s : GL (Fin D.R.r) (Fb (D.what₂.places.resChar (D.nd.w i))
      (D.what₂.places.resChar_prime (D.nd.w i)))) : Matrix (Fin D.R.r) (Fin D.R.r)
      (Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i)))).charpoly =
      (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective
      (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom
      (RingHom.injective _)
    rw [h4, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  have h6 : s ∈ (D.ntypes.rbar σ (D.nd.w i)).ker := by
    refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _ inferInstance
      (D.ntypes.rbar_open σ _) s ((D.what₂.places.resChar (D.nd.w i)) ^ D.R.r) (fun hmem => hw ?_) hwild ?_
    · rw [Nat.cast_pow, D.nd.w_l i] at hmem
      exact (D.naut.plGw k v).isPrime.mem_of_pow_mem _ hmem
    · rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
      exact GlobalTheory.TameLabels.pow_eq_one_of_charpoly _ h5
  exact h6

end GlobalTheory.RowWildTame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRestrictEqTopOfAbsIrrSub
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BurnsideSub

theorem matRep_apply {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (g : Γ)
    (v : Fin a → k) :
    matRep ((Units.coeHom _).comp ρ) g v = (ρ g : Matrix (Fin a) (Fin a) k).mulVec v := by
  simp [matRep]

theorem isIrrSub_top_of_intertwine {K Γ : Type} [Field K] [Group Γ] {a d : ℕ}
    (ρ : Γ →* GL (Fin a) K) (σ : Γ →* GL (Fin d) K) (B : Matrix (Fin a) (Fin d) K)
    (C : Matrix (Fin d) (Fin a) K) (hCB : C * B = 1)
    (hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) K) * B = B * (σ g : Matrix (Fin d) (Fin d) K))
    (h : IsIrrSub ρ (LinearMap.range B.mulVecLin)) : IsIrrSub σ ⊤ := by
  have hinj : Function.Injective B.mulVecLin := by
    intro x y hxy
    have := congrArg C.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hCB] using this
  have hmap : ∀ U : Submodule K (Fin d → K), (∀ g, ∀ v ∈ U, (σ g : Matrix (Fin d) (Fin d) K).mulVec v ∈ U) →
      IsInv ρ (U.map B.mulVecLin) := by
    rintro U hU g _ ⟨v, hv, rfl⟩
    refine ⟨_, hU g v hv, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint g]
  refine ⟨fun h0 => h.1 ?_, fun g v _ => trivial, fun U _ hU => ?_⟩
  · rw [LinearMap.range_eq_map, h0, Submodule.map_bot]
  · have hle : U.map B.mulVecLin ≤ LinearMap.range B.mulVecLin := LinearMap.map_le_range
    rcases h.2.2 _ hle (hmap U hU) with h1 | h1
    · left
      exact Submodule.map_injective_of_injective hinj (h1.trans (Submodule.map_bot _).symm)
    · right
      rw [LinearMap.range_eq_map] at h1
      exact Submodule.map_injective_of_injective hinj h1

theorem span_restrict_eq_top_of_absIrrSub : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W),
    AbsIrrSub ρ W →
    Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  intro k Γ _ _ a ρ W hW habs
  classical
  set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ
  let r : Γ → Module.End k W := fun g => (τ g).restrict (hW g)
  have hr1 : r 1 = 1 := by
    ext v; simp [r]
  have hrm : ∀ g h, r (g * h) = r g * r h := by
    intro g h; ext v; simp [r]
  let d := Module.finrank k W
  let e : W ≃ₗ[k] (Fin d → k) := (Module.finBasis k W).equivFun

  let φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k :=
    e.conj.trans LinearMap.toMatrix'
  have hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ
      (e.symm : (Fin d → k) →ₗ[k] W)) := fun _ => rfl
  have hφ1 : φ 1 = 1 := by
    rw [hφa]
    have : (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ
        (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id := LinearMap.ext fun v => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hφm : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    rw [hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun v => by simp
  let S : Γ →* Matrix (Fin d) (Fin d) k :=
    { toFun := fun g => φ (r g)
      map_one' := by rw [hr1, hφ1]
      map_mul' := fun g h => by rw [hrm, hφm] }
  let σ : Γ →* GL (Fin d) k := MonoidHom.toHomUnits S
  have hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g) := fun g => rfl

  let L : (Fin d → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ e.symm.toLinearMap
  have hLinj : Function.Injective L := by
    intro x y hxy
    exact e.symm.injective (Subtype.val_injective hxy)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective L (LinearMap.ker_eq_bot.2 hLinj)
  let B : Matrix (Fin a) (Fin d) k := LinearMap.toMatrix' L
  let C : Matrix (Fin d) (Fin a) k := LinearMap.toMatrix' L'
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]
  have hBv : ∀ c, B.mulVec c = L c := fun c => LinearMap.toMatrix'_mulVec L c
  have hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k) := by
    intro g
    have hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g) := by
      have : τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) :=
        LinearMap.ext fun v => by rw [hτ, matRep_apply, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix'_toLin']
    rw [hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun c => ?_
    change τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)
    rw [e.symm_apply_apply]
    rfl
  set f := algebraMap k (AlgebraicClosure k) with hf
  have hspan : Submodule.span (AlgebraicClosure k) ((fun v => f ∘ v) '' W) =
      LinearMap.range (B.map f).mulVecLin := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨f ∘ e ⟨w, hw⟩, ?_⟩
      funext i
      have h1 : B.mulVec (e ⟨w, hw⟩) = w := by
        rw [hBv]
        change ((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w
        rw [e.symm_apply_apply]
      rw [Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]
      rfl
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [op_smul_eq_smul]
      refine Submodule.smul_mem _ _ ?_
      apply Submodule.subset_span
      refine ⟨L (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩
      funext i
      simp [← hBv, Matrix.mulVec_single_one]
  unfold AbsIrrSub at habs
  rw [hspan] at habs
  have hirr : IsIrrSub (mapRep f σ) ⊤ := by
    refine isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f) (C.map f) ?_ ?_ habs
    · rw [← Matrix.map_mul, hCB]
      exact Matrix.map_one _ f.map_zero f.map_one
    · intro g
      change (ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f =
        B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f
      rw [← Matrix.map_mul, ← Matrix.map_mul, hint g]
  have h2 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) = fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map f := by
    funext g
    ext p q
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep]
  rw [h3] at h2
  have h4 := GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2
  have h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r := by
    rw [← Set.range_comp]; rfl
  have h6 := Submodule.map_span φ.toLinearMap (Set.range r)
  change Submodule.span k (Set.range r) = ⊤
  refine Submodule.map_injective_of_injective φ.injective ?_
  rw [h6, Submodule.map_top, LinearEquiv.range]
  rw [h5] at h4
  exact h4

end GlobalTheory.BurnsideSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordClusterDepthLongOrbitStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf φ.2 → (pageWord L j ε τ φ).HypA (depth L l) := by
  first | exact @GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit | exact GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit | (intros; apply GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordInertPrimeDichotomyStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_inert_prime_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → φ.1.2 = -1 → (pageWord L j ε τ φ).Box ∧ ((pageWord L j ε τ φ).HypNT ∨ (φ = D.R.cc ∧ (pageWord L j ε τ φ).HypAT l ∧ ∀ i, (pageWord L j ε τ φ).thick i)) := by
  first | exact @GlobalTheory.HTW.pageWord_inert_dichotomy | exact GlobalTheory.HTW.pageWord_inert_dichotomy | (intros; apply GlobalTheory.HTW.pageWord_inert_dichotomy <;> assumption)
end

