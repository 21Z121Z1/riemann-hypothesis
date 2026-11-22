import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3365
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0822
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0708
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0735
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0809
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartDerivationBoundaryParamMemSpan
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDerBd

theorem X_dvd_of_X_mul {σ K : Type} [Field K] {s t : σ} (hst : t ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ MvPowerSeries.X t * g) : MvPowerSeries.X s ∣ g := by
  classical
  rw [MvPowerSeries.X_dvd_iff] at h ⊢
  intro n hn
  have h1 := h (n + Finsupp.single t 1) (by simp [Finsupp.single_apply, hst, hn])
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul] at h1
  simpa using h1

theorem X_dvd_of_prod_mul {σ K : Type} [Field K] {Idx : Type} (f : Idx → σ) {s : σ}
    (S : Finset Idx) (hS : ∀ j ∈ S, f j ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ (∏ j ∈ S, MvPowerSeries.X (f j)) * g) : MvPowerSeries.X s ∣ g := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, _root_.mul_assoc] at h
    exact ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
      (X_dvd_of_X_mul (hS a (Finset.mem_insert_self a S)) h)

theorem deriv_bdParam_mem_span : ∀ (A : Type) [CommRing A] (k : Type) [Field k] (m d : ℕ) (ψ : A →+* ChartRing k m d) (δ : Derivation ℤ A A) (D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (I : Ideal A), (∀ a ∈ I, δ a ∈ I) → (∀ a, D' (ψ a) = ψ (δ a)) → I.map ψ = Ideal.span {∏ i, bdParam k m d i} → ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  classical
  intro A _ k _ m d ψ δ D' I hI hD hJ i

  have hpres : ∀ x ∈ I.map ψ, D' x ∈ I.map ψ := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hD]
      exact Ideal.mem_map_of_mem ψ (hI a ha)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    | smul r x hxm hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ r hx)
        (Ideal.mul_mem_right _ _ (Ideal.span_le.2 (fun y hy => Ideal.subset_span hy) hxm))
  set t := bdParam k m d with ht
  have hP : t i * ∏ j ∈ Finset.univ.erase i, t j = ∏ j, t j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hmem : D' (∏ j, t j) ∈ Ideal.span {∏ j, t j} := by
    rw [← hJ]; apply hpres; rw [hJ]; exact Ideal.subset_span rfl
  rw [Ideal.mem_span_singleton] at hmem ⊢
  rw [← hP, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hmem
  have h1 : t i ∣ t i * D' (∏ j ∈ Finset.univ.erase i, t j) + (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_mul_right (t i) _).trans hmem
  have h2 : t i ∣ (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_add_right (dvd_mul_right _ _)).1 h1
  exact X_dvd_of_prod_mul (fun j : Fin m => (Sum.inl j : Fin m ⊕ Fin d)) (Finset.univ.erase i)
    (fun j hj h => (Finset.ne_of_mem_erase hj) (Sum.inl_injective h)) h2

end GlobalTheory.ChartDerBd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtAlg

theorem valR_eq' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_add' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f + g) = valR x U f + valR x U g := by
  simp only [valR_eq' x U h, map_add]

theorem valR_sub' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f - g) = valR x U f - valR x U g := by
  simp only [valR_eq' x U h, map_sub]

theorem valR_mul'' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq' x U h, map_mul]

theorem valR_zero' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) :
    valR x U (0 : Γ(X, U)) = 0 := by
  unfold valR; split_ifs <;> simp

theorem valR_natCast' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (m : ℕ) : valR x U (m : Γ(X, U)) = m := by
  simp only [valR_eq' x U h, map_natCast]

theorem appLE_congr_top {P P' : Scheme.{0}} (b b' : P ⟶ P') (e : b = b') (h h') :
    b.appLE ⊤ ⊤ h = b'.appLE ⊤ ⊤ h' := by
  subst e; rfl

theorem valR_constFn_congr {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (x x' : Sp A ⟶ X) (p : X ⟶ Sp B)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : x ≫ p = x' ≫ p) (r : B) :
    valR x U (constFn p U r) = valR x' U (constFn p U r) := by
  have key : ∀ (b : Sp A ⟶ X) (hb : ⊤ ≤ b ⁻¹ᵁ U) (y : Γ(Sp B, ⊤)),
      (b.appLE U ⊤ hb).hom ((p.appLE ⊤ U (fun _ _ => trivial)).hom y) = ((b ≫ p).appLE ⊤ ⊤ (fun _ _ => trivial)).hom y := by
    intro b hb y
    rw [← Scheme.Hom.appLE_comp_appLE]; rfl
  rw [valR_eq' x U h, valR_eq' x' U h', constFn, key, key]
  have hh := appLE_congr_top (x ≫ p) (x' ≫ p) e (fun _ _ => trivial) (fun _ _ => trivial)
  rw [hh]

theorem rsT_self {X : Scheme.{0}} {O : X.Opens} (s : Γ(X, O)) : rsT s O = s := by
  simp [rsT, resG]

end GlobalTheory.Heat.WtAlg

namespace GlobalTheory.Heat.WtAlg

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem c_zero {S : Type} [CommRing S] {φ : R →+* S} (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) :
    c 0 = 1 := by
  have hu : unitOn (c 0) = 1 := unit_ext fun y _ => by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e := hc 0 y J hJ
    rw [(val_corr hJ (Y.Φ _ x').s_zero _).trans (val_one _), (val_corr hJ (Y.Φ _ x).s_zero _).trans (val_one _),
      _root_.mul_one] at e
    rw [map_one]; exact e.symm
  have := congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu
  simp only [unitOn, Units.coe_map, Units.val_one, map_one] at this
  exact Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans this)

theorem isWt_add {α : Q.X} {V : Y.H.left.Opens} {f g : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hg : IsWt Y α V g) :
    IsWt Y α V (f + g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_add' _ _ hV', valR_add' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    hg S φ x x' c a a' ha ha' hV hV' hq hc, mul_add]

theorem isWt_sub {α : Q.X} {V : Y.H.left.Opens} {f g : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hg : IsWt Y α V g) :
    IsWt Y α V (f - g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_sub' _ _ hV', valR_sub' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    hg S φ x x' c a a' ha ha' hV hV' hq hc, mul_sub]

theorem isWt_zero (α : Q.X) (V : Y.H.left.Opens) : IsWt Y α V 0 := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_zero', valR_zero', mul_zero]

theorem isWt_sum {α : Q.X} {V : Y.H.left.Opens} {I : Type} (s : Finset I) (f : I → Γ(Y.H.left, V))
    (hf : ∀ i ∈ s, IsWt Y α V (f i)) : IsWt Y α V (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IsWt Y α V) (fun _ _ => isWt_add) (isWt_zero α V) hf

theorem isRaynaudTorusWeightFunction_weightZero_mul {α : Q.X} {V : Y.H.left.Opens} {g f : Γ(Y.H.left, V)} (hg : IsWt Y 0 V g) (hf : IsWt Y α V f) :
    IsWt Y α V (g * f) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc,
    hf S φ x x' c a a' ha ha' hV hV' hq hc, c_zero x x' c hc, Units.val_one, _root_.one_mul]
  ring

theorem isWt_natCast (V : Y.H.left.Opens) (m : ℕ) : IsWt Y 0 V (m : Γ(Y.H.left, V)) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_natCast' _ _ hV', valR_natCast' _ _ hV, c_zero x x' c hc, Units.val_one, _root_.one_mul]

theorem isWt_constFn (V : Y.H.left.Opens) (r : R) : IsWt Y 0 V (constFn Y.H.hom V r) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  rw [valR_constFn_congr x'.left x.left Y.H.hom V hV' hV ((Over.w x').trans (Over.w x).symm) r,
    c_zero x x' c hc, Units.val_one, _root_.one_mul]

end GlobalTheory.Heat.WtAlg

namespace GlobalTheory.Heat.WtAlg

theorem op_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R) (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (k : ℕ) (α : Q.X) (f : Γ(Y.H.left, h.W i)), IsWt Y α (h.W i) f → IsWt Y α (h.W i) (op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h hdd hB i k α f hf
  obtain ⟨⟨V, hV⟩, hp, hp', hd⟩ := hB i
  have key : ∀ g : Γ(Y.H.left, h.W i), IsWt Y α (h.W i) g → IsWt Y α (h.W i) (h.d i (h.W i) g) := by
    have := hd α V hV.ge
    rw [← hV] at this
    exact this
  have h2 : IsWt Y 0 (h.W i) (2 : Γ(Y.H.left, h.W i)) := by simpa using isWt_natCast (Y := Y) (h.W i) 2
  have hk : IsWt Y 0 (h.W i) (k : Γ(Y.H.left, h.W i)) := isWt_natCast (h.W i) k
  have hk2 : IsWt Y 0 (h.W i) ((k : Γ(Y.H.left, h.W i)) ^ 2) := by rw [sq]; exact isRaynaudTorusWeightFunction_weightZero_mul hk hk
  have hrp : IsWt Y 0 (h.W i) (rsT (h.p i) (h.W i)) := by rw [rsT_self]; exact hp
  have hrp' : IsWt Y 0 (h.W i) (rsT (h.p' i) (h.W i)) := by rw [rsT_self]; exact hp'
  unfold op
  refine isWt_add (isWt_add (isWt_sub ?_ ?_) ?_) ?_
  · exact isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk) (key f hf)
  · exact isWt_sum _ _ fun a _ => isWt_sum _ _ fun b _ =>
      isRaynaudTorusWeightFunction_weightZero_mul (isWt_constFn _ _) (hdd _ _ _ _ (hdd _ _ _ _ hf))
  · exact isRaynaudTorusWeightFunction_weightZero_mul h2 (isWt_sum _ _ fun a _ => isRaynaudTorusWeightFunction_weightZero_mul (isWt_constFn _ _) (hdd _ _ _ _ hf))
  · exact isRaynaudTorusWeightFunction_weightZero_mul (isWt_add (isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk2) hrp) (isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk) hrp')) hf

end GlobalTheory.Heat.WtAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedKernelLeThetaFunctionRouteBigVertex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.ZConvIdent
open GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem conjU_mul {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) (g k : GA D V) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h (g * k) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h k := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_mul]

theorem thetaSum_finset_sum {F : Type} [Field F] [NumberField F] {κ ι : Type} [Fintype κ] (s : Finset ι)
    (f : ι → (κ → AdeleRing (𝓞 F) F) → ℂ) (hf : ∀ k ∈ s, f k ∈ schA F κ) :
    thetaSum F (∑ k ∈ s, f k) = ∑ k ∈ s, thetaSum F (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      thetaSum_add F (hf a (Finset.mem_insert_self a s)) (Submodule.sum_mem _ fun k hk => hf k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]

theorem translates_kerSmall_le_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ (z : GA D (G.V (.grid i j)) →₀ ℂ) (Φ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank +
        (G.V (.grid i j)).rank) → AF D.host.F) → ℂ) (a : GA D (G.V (.grid i j)) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB Γ.V'.J) (C₀ : ℝ),
      zdeg z ≠ 0 ∧ Φ ∈ Γ.M'.So Bs.ψ Bs.τ₁ ∧
      ∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
        C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁))‖ := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ΦB, hB, z, hz, hS⟩ := GlobalTheory.T.exists_routeDatum_translationCombination_goodPlace hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ξ, hξ, hk⟩ := GlobalTheory.T.small_route_kernel_eq_unit_norm_mul_theta hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv ΦB hB
  refine ⟨z, _, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁, 1, hz, hS, fun g u => le_of_eq ?_⟩
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have hpres : ∀ p φ, φ ∈ schA D.host.F _ → om' p φ ∈ schA D.host.F _ := fun p φ hφ => hW.pres p φ hφ
  have hB0 := hB.1
  set a := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁
  set hh := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)
  have ha : ∀ x y, a (x * y) = a x * a y := conjU_mul _ _ _
  have e1 : translates z (kerSmall W Θ' g g₁) u =
      ξ (g, g₁) * z.sum fun k c => c * thetaSum D.host.F (om' (a u, hh) (om' (a k, 1) ΦB)) := by
    rw [translates, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [hk, ha, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    ring
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' (z.sum fun k c => c • om' (a k, 1) ΦB) (a u) hh =
      z.sum fun k c => c * thetaSum D.host.F (om' (a u, hh) (om' (a k, 1) ΦB)) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_finsuppSum, Finsupp.sum, thetaSum_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, thetaSum_smul]
    · intro k _
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hpres _ _ (hpres _ _ hB0))
  rw [e1, e2, norm_mul, hξ, one_mul]

end GlobalTheory.ZConvIdent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TvELeft
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.VertCoeffRing
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def tvE (u : TanM (𝟙 (Sp R)) G) : epsR R ⟶ G := Over.homMk (tv u).left (by
  have := Over.w (tv u)
  simpa using this)

theorem tvE_left (u : TanM (𝟙 (Sp R)) G) : (tvE u).left = (tv u).left := rfl

end GlobalTheory.VertCoeffRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTangentBasisOfRaynaudBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanRay

open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv_mem mkT tv_mkT tanM_ext tv_add tv_smul)

theorem tanBasis_of_isPointOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ∀ a, b a = v' a := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH v' hv
  have hc : IsAdicComplete ((maximalIdeal R).map (algebraMap R (DualNumber R))) (DualNumber R) := by
    have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
    exact GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hT : GlobalTheory.AdicColimit.IsAdicColimit (maximalIdeal R) (overAt (𝟙 (Sp R)) (DualNumber R)) := by
    refine GlobalTheory.AdicColimit.IsAdicColimit.of_iso (Over.isoMk (Iso.refl _) ?_)
      (GlobalTheory.AdicColimit.isAdicColimit_spec_of_isLocalRing R (maximalIdeal R) (DualNumber R)
        (algebraMap R (DualNumber R)) hc)
    simp
  have hΦ := Y.rep
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusModel.exists_mulEquiv P.U.toUnifPre GlobalTheory.allSixLaws.1.globalFns hΦ
  have nat : ∀ (k : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ overAt (𝟙 (Sp R)) (DualNumber R))
      (w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ Y.H), J _ hT (k ≫ w) = k ≫ J _ hT w := fun k w =>
    (hJ _ hT _ _).2 (((hJ _ hT w _).1 rfl).pull k (hΦ.1 _ _ k _))
  have hs : ∀ (a : R) (w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ Y.H),
      J _ hT (smT (𝟙 (Sp R)) a w) = smT (𝟙 (Sp R)) a (J _ hT w) := fun a w => nat _ w
  have mem : ∀ v : TanM (𝟙 (Sp R)) Y.H, smT (𝟙 (Sp R)) 0 (J _ hT (tv v)) = 1 := fun v => by
    rw [← hs, tv_mem, map_one]
  let L : TanM (𝟙 (Sp R)) Y.H →ₗ[R] TanM (𝟙 (Sp R)) t.G :=
    { toFun := fun v => mkT (J _ hT (tv v)) (mem v)
      map_add' := fun u v => tanM_ext (by
        simp only [tv_mkT, tv_add, map_mul])
      map_smul' := fun a v => tanM_ext (by
        simp only [tv_mkT, tv_smul, RingHom.id_apply, hs]) }
  have hL : Function.Bijective L := by
    refine ⟨fun u v h => tanM_ext ((J _ hT).injective ?_), fun w => ?_⟩
    · have := congrArg tv h
      simpa [L, tv_mkT] using this
    · have h0 : smT (𝟙 (Sp R)) 0 ((J _ hT).symm (tv w)) = 1 := by
        apply (J _ hT).injective
        rw [hs, MulEquiv.apply_symm_apply, tv_mem, map_one]
      refine ⟨mkT _ h0, tanM_ext ?_⟩
      show J _ hT ((J _ hT).symm (tv w)) = tv w
      exact MulEquiv.apply_symm_apply _ _
  refine ⟨vH.map (LinearEquiv.ofBijective L hL), fun a => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply]
  refine tanM_ext ?_
  exact (hJ _ hT _ _).2 (hv a)

end GlobalTheory.TanRay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTripleAbelianLocusProperRelAmple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem relAmple_local {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O]
    (t : SAB H (Sp O)) (hprop : IsProper t.G.hom) (hpol : GlobalTheory.LN.PolAt t (Out.jK O)) :
    Out.RelAmple t.G t.PP.L := by
  by_cases hf : _root_.IsField O
  · obtain ⟨u, ⟨mu⟩⟩ := GlobalTheory.PolLocal.exists_pull (Out.jK O) t
    obtain ⟨hA, hK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mu hpol
    haveI : IsIso (Out.jK O) := GlobalTheory.PolLocal.isIso_spMap _ (GlobalTheory.PolLocal.algebraMap_fractionRing_bijective O hf)
    exact (GlobalTheory.PolLocal.ample_kTriv_of_iso mu hA hK).1
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap ρ) t
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap V (FractionRing V))) tV
  have hpV : GlobalTheory.LN.PolAt tV (Out.jK V) := GlobalTheory.PolNormal.polAt_generic_pull ρ hρ mV hpol
  obtain ⟨hAK, hKK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mK hpV
  obtain ⟨hAV, hKV⟩ := GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre GlobalTheory.HomExtExamples.homExtSt_holds GlobalTheory.allSixLaws.1
    GlobalTheory.allSixLaws.2.1 E H V (FractionRing V) tV tK mK (GlobalTheory.PolLocal.isProper_of_map mV hprop) hAK hKK
  obtain ⟨uk, ⟨mk⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (IsLocalRing.residue V)) tV
  obtain ⟨hAk, hKk⟩ := GlobalTheory.PolLocal.pull_ample_kTriv mk hAV hKV
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mV mk
  let β : O →+* IsLocalRing.ResidueField V := (IsLocalRing.residue V).comp ρ
  have hpβ : GlobalTheory.LN.PolAt t (spMap β) := by
    rw [GlobalTheory.PolLocal.spMap_comp]
    exact GlobalTheory.LocM.PolFibre.polAt_of_map n (by haveI := hprop; infer_instance) hAk hKk
  obtain ⟨r, hr, hA⟩ := GlobalTheory.PolNearAmple.relAmple_near_of_polAt E H O t hprop (IsLocalRing.ResidueField V) β hpβ
  have hu : IsUnit r := isUnit_of_map_unit ρ r ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hr)
  obtain ⟨m₀, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  have e : spMap (RingHom.id O) = 𝟙 (Sp O) := by
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact hA O (RingHom.id O) hu t (e ▸ m₀)

theorem relAmple_kTriv_of_generic {S : Type} [CommRing S] [IsDomain S] [CharZero S] [IsNoetherianRing S]
    (t : SAB H (Sp S)) (hp : IsProper t.G.hom) (hg : GlobalTheory.LN.PolAt t (Out.jK S)) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  have hA : Out.RelAmple t.G t.PP.L := by
    have := t.semi.quasiCompact
    have := t.semi.separated
    refine GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance fun q => ?_
    have : q.asIdeal.IsPrime := q.isPrime
    let O := Localization.AtPrime q.asIdeal
    obtain ⟨tO, ⟨m⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap S O)) t
    have hi : Function.Injective (algebraMap S O) :=
      IsLocalization.injective O q.asIdeal.primeCompl_le_nonZeroDivisors
    have : CharZero O := charZero_of_injective_algebraMap hi
    have hA := relAmple_local tO (GlobalTheory.PolLocal.isProper_of_map m hp) (GlobalTheory.PolNormal.polAt_generic_pull _ hi m hg)
    obtain ⟨w, hw, -⟩ := m.lin
    exact GlobalTheory.AmpleSpreadAt.relAmple_spread_at S q t.G t.PP.L hp t.PP.isLB tO.G m.φ tO.PP.L m.cart.1 tO.PP.isLB
      ⟨w, hw⟩ hA
  exact ⟨hA, GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic E H S t hp hA hg⟩

theorem isProper_relAmple_kTriv_of_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (S : Scheme.{0}) (x : S ⟶ Sp R) (t' : SAB H S), (∀ s : S, ∏ i, tt i ∉ (x s).asIdeal) → Nonempty (SABMap t' t x) → IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab S x t' hx ⟨mx⟩
  have : CharZero R := algebraRat.charZero R
  have hf : ∏ i, tt i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  generalize ∏ i, tt i = f at hf hab hx
  let Rf := Localization.Away f
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hi : Function.Injective (algebraMap R Rf) := IsLocalization.injective Rf hle
  have : IsDomain Rf := IsLocalization.isDomain_localization hle
  have : CharZero Rf := charZero_of_injective_algebraMap hi
  obtain ⟨tf, ⟨mf⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap R Rf)) t
  have hrange : Set.range (spMap (algebraMap R Rf)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range Rf f
  have habf : abLocus tf.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi mf.cart.1 z).1 ((hab _).2 (hrange.le ⟨z, rfl⟩))
  have hg : GlobalTheory.LN.PolAt tf (Out.jK Rf) := GlobalTheory.PolNormal.polAt_generic_pull _ hi mf (GlobalTheory.DatUniq.polAt_of_unif P)
  have hpf : IsProper tf.G.hom := GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H Rf tf hg habf
  obtain ⟨hA, hK⟩ := relAmple_kTriv_of_generic tf hpf hg
  have : IsOpenImmersion (spMap (algebraMap R Rf)) := by
    unfold spMap
    exact IsOpenImmersion.of_isLocalization f
  have hr : Set.range x ⊆ Set.range (spMap (algebraMap R Rf)) := by
    rintro _ ⟨s, rfl⟩
    exact hrange.ge (hx s)
  obtain ⟨m', -⟩ := GlobalTheory.ArcObj.exists_sab_fac mf mx (g := IsOpenImmersion.lift _ x hr)
    (IsOpenImmersion.lift_fac _ _ hr).symm
  obtain ⟨w, hw, -⟩ := m'.lin
  exact ⟨GlobalTheory.PolLocal.isProper_of_map m' hpf,
    GlobalTheory.AmpleLocalBase.relAmple_baseChange m'.cart.1 tf.PP.isLB t'.PP.isLB ⟨w, hw⟩ hA,
    kTriv_pull m'.cart tf.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) hK⟩

end GlobalTheory.AbLocusPol
end

