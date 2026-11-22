import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupLatticeIsLatInStable
section
set_option autoImplicit false

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

section General

variable {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K]
  {C : Type} [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}

omit [NumberField K] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] in

theorem coord_one_tmul_smul (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (r : F) (f : C) :
    z.symm (1 ⊗ₜ[F] (r • f)) = algebraMap F K r • z.symm (1 ⊗ₜ[F] f) := by
  rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    Algebra.smul_def, smul_eq_mul]

theorem spanK_span (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (s : Set C) :
    spanK z (Submodule.span (𝓞 F) s : Set C) = spanK z s := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hi : IsIntegral ℤ (algebraMap F K (r : F)) :=
        (RingOfIntegers.isIntegral_coe r).map (algebraMap F K).toIntAlgHom
      have e : z.symm (1 ⊗ₜ[F] (r • x)) = (⟨algebraMap F K (r : F), hi⟩ : 𝓞 K) • z.symm (1 ⊗ₜ[F] x) := by
        rw [← algebraMap_smul F r x, coord_one_tmul_smul]
        rfl
      simp only [e]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem spanK_isLatIn (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (M : Submodule (𝓞 F) C) (hfg : M.FG)
    (htop : Submodule.span F (M : Set C) = ⊤) : Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (spanK z (M : Set C)) := by
  constructor
  · obtain ⟨s, rfl⟩ := hfg
    rw [spanK_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · have h1 : ∀ f : C, z.symm (1 ⊗ₜ[F] f) ∈ Submodule.span K (spanK z (M : Set C) : Set (Fin n → K)) := by
      intro f
      have hf : f ∈ Submodule.span F (M : Set C) := htop ▸ Submodule.mem_top
      induction hf using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [TensorProduct.tmul_add, map_add]
        exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        rw [coord_one_tmul_smul]
        exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, rfl⟩ := z.symm.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul k f =>
      have e : (k ⊗ₜ[F] f : K ⊗[F] C) = k • (1 ⊗ₜ[F] f) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, map_smul]
      exact Submodule.smul_mem _ _ (h1 f)
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ (hx trivial) (hy trivial)

end General

theorem supLattice_isLatIn_stable : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → Submodule.IsLattice B.KO (B.Mlat j ka) → (∀ g, ∀ F ∈ B.Mlat j ka, act g F ∈ B.Mlat j ka) → Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Ms i) ∧ ∀ g : P, (O.Ms i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Ms i := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act h hL hact
  rw [h.Ms_eq]
  refine ⟨spanK_isLatIn z _ hL.fg hL.span_eq_top, fun g => ?_⟩
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  show O.ρ i g (z.symm (1 ⊗ₜ f)) ∈ spanK z _
  rw [h.rho_eq]
  exact Submodule.subset_span ⟨act g f, hact g f hf, rfl⟩

end GlobalTheory.FormTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaScaledSpanLeSigmaSmulUnscaledSpan
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.ScaledSpan

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def sc (s : R) (N : Submodule R A) : Submodule R A := N.map (s • LinearMap.id)

theorem mem_sc {s : R} {N : Submodule R A} {x : A} : x ∈ sc s N ↔ ∃ y ∈ N, x = s • y := by
  simp [sc, eq_comm]

theorem sc_mul_le {s t : R} {M M' N N' : Submodule R A} (h : M ≤ sc s M') (h' : N ≤ sc t N') :
    M * N ≤ sc (s * t) (M' * N') := by
  refine Submodule.mul_le.2 fun m hm n hn => ?_
  obtain ⟨a, ha, rfl⟩ := mem_sc.1 (h hm)
  obtain ⟨b, hb, rfl⟩ := mem_sc.1 (h' hn)
  exact mem_sc.2 ⟨a * b, Submodule.mul_mem_mul ha hb, smul_mul_smul_comm s a t b⟩

theorem sc_pow_le {s : R} {M M' : Submodule R A} (h : M ≤ sc s M') (n : ℕ) :
    M ^ n ≤ sc (s ^ n) (M' ^ n) := by
  induction n with
  | zero => intro x hx; exact mem_sc.2 ⟨x, by simpa using hx, by simp⟩
  | succ n ih => rw [pow_succ, pow_succ, pow_succ]; exact sc_mul_le ih h

theorem sc_le_of_dvd {s t : R} {M N : Submodule R A} (hd : t ∣ s) (h : M ≤ N) : sc s M ≤ sc t N := by
  obtain ⟨c, rfl⟩ := hd
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_sc.1 hx
  exact mem_sc.2 ⟨c • y, N.smul_mem c (h hy), mul_smul t c y⟩

end General

variable {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem emb_WWc_le (X : WeightAlgebra.PJ D B P6 j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) :
    X.emb w (X.WWc s w) ≤ sc s (X.emb w (X.thAll w)) := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact mem_sc.2 ⟨_, ⟨y, hy, rfl⟩, by simp⟩

theorem emb_Thc_le (X : WeightAlgebra.PJ D B P6 j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) :
    X.emb w (X.Thc s w) ≤
      sc (s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n)) (X.emb w (X.shortTh w)) := by
  rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  refine mem_sc.2 ⟨_, ⟨y, hy, rfl⟩, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, mul_smul]
  exact smul_comm _ _ _

theorem nnW_eq (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {ka wL wF : WeightFamilies.Wt D j} {T n : ℕ} (h : WeightAlgebra.IsF' ka wL wF T n) :
    nnW B hinj EX ka = nnW B hinj EX wL ^ T * nnW B hinj EX wF := by
  obtain ⟨-, hP, hM⟩ := h
  have hP' : ∀ τ i, ka.aP τ i = wL.aP τ i * T + wF.aP τ i := fun τ i => by
    have := hP τ i
    zify
    linarith
  have hM' : ∀ τ i, ka.aM τ i = wL.aM τ i * T + wF.aM τ i := fun τ i => by
    have := hM τ i
    zify
    linarith
  have h1 : Dplus ka = Dplus wL * T + Dplus wF := by
    simp only [Dplus, hP', Finset.sum_add_distrib, Finset.sum_mul]
  have h2 : Dminus ka = Dminus wL * T + Dminus wF := by
    simp only [Dminus, hM', Finset.sum_add_distrib, Finset.sum_mul]
  simp only [nnW, h1, h2, Fin.prod_univ_two]
  ring

theorem nnW_ne_zero (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (w : WeightFamilies.Wt D j) : nnW B hinj EX w ≠ 0 := by
  have hn : ∀ i, EX.piG i * piBarO EX i = (D.host.g i : 𝓞 D.host.E) := fun i => by
    apply Subtype.ext
    exact EX.piG_norm i
  have hn' : ∀ i, iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) ≠ 0 := fun i => by
    rw [← map_mul, hn, map_natCast]
    exact_mod_cast (D.host.g_prime i).ne_zero
  exact Finset.prod_ne_zero_iff.2 fun i _ =>
    mul_ne_zero (pow_ne_zero _ (left_ne_zero_of_mul (hn' i))) (pow_ne_zero _ (right_ne_zero_of_mul (hn' i)))

theorem theta_le_sigma_smul : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ), WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → sigRec B hinj EX ka wL wF T ≠ 0 ∧ ∀ F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T, ∃ G ∈ thetaPlain X ka wL wF T, F = sigRec B hinj EX ka wL wF T • G := by
  intro D B P6 j X hinj EX p ka wL wF T hF hn hT
  refine ⟨?_, fun F hF' => mem_sc.1 (?_ : F ∈ sc _ _)⟩
  · refine mul_ne_zero (nnW_ne_zero B hinj EX ka) (Nat.cast_ne_zero.2 ?_)
    have hq : D.host.q ≠ 0 := (D.host.hyp.1 : D.host.q.Prime).ne_zero
    have hd : D.host.d ≠ 0 := (D.host.hyp.2.1 : D.host.d.Prime).ne_zero
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    have hS : D.host.QS ≠ 0 := D.host.QS_pos.ne'
    unfold pPow
    positivity
  · revert F
    change X.Theta _ ka wL wF T ≤ _
    have hnn := nnW_eq B hinj EX hF
    refine sup_le (sup_le ?_ ?_) ?_
    · refine (sc_mul_le (sc_pow_le (emb_WWc_le X _ wL) T) (emb_Thc_le X _ wF)).trans
        (sc_le_of_dvd ⟨(zOwnP D p wF : 𝓞 B.KO), ?_⟩ (le_sup_left.trans le_sup_left))
      simp only [scalOfP, sigRec, hnn, pPow]
      push_cast
      ring
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
      refine (sc_mul_le (sc_pow_le (emb_WWc_le X _ wL) _) (emb_Thc_le X _ _)).trans
        (sc_le_of_dvd ⟨(zOwnP D p (X.wF0 wL wF) : 𝓞 B.KO) *
          ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * (WeightFamilies.dimY D j * wL.n)), ?_⟩
          (le_sup_right.trans le_sup_left))
      have e : (X.wF0 wL wF).n = wF.n + WeightFamilies.dimY D j * wL.n := rfl
      simp only [scalOfP, sigRec, hnn, pPow, e, Nat.add_sub_cancel_left]
      unfold WeightAlgebra.PJ.wF0
      push_cast
      ring
    · refine (emb_Thc_le X _ ka).trans
        (sc_le_of_dvd ⟨(zOwnP D p ka : 𝓞 B.KO) *
          ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * (T * wL.n)), ?_⟩ le_sup_right)
      simp only [scalOfP, sigRec, hnn, pPow, hn]
      push_cast
      ring

end GlobalTheory.ScaledSpan
end

