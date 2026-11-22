import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0108
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicRealisationHolomorphicMap
section
open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.CentSep

theorem apply_basis_eq_smul {L V κ : Type} [Field L] [AddCommGroup V] [Module L V]
    (b : Module.Basis κ L V) (μ : κ → L) (hμ : Function.Injective μ)
    (f g : Module.End L V) (hf : ∀ k, f (b k) = μ k • b k) (hg : g ∘ₗ f = f ∘ₗ g) (k : κ) :
    ∃ c : L, g (b k) = c • b k := by
  refine ⟨b.repr (g (b k)) k, ?_⟩
  set x := g (b k) with hx
  have hfx : f x = μ k • x := by
    have := congrArg (fun φ : Module.End L V => φ (b k)) hg
    simp only [LinearMap.comp_apply, hf] at this
    rw [hx, ← this, map_smul]
  have hrep : ∀ y : V, ∀ j, b.repr (f y) j = μ j * b.repr y j := by
    intro y j
    have key : (b.coord j).comp f = μ j • b.coord j := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply, hf, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        LinearMap.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs with h
      · subst h; rfl
      · simp
    exact congrArg (fun φ : V →ₗ[L] L => φ y) key
  apply b.ext_elem
  intro j
  by_cases hj : j = k
  · subst hj; simp
  · have h1 := hrep x j
    rw [hfx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have h0 : b.repr x j = 0 := by
      have h2 : (μ j - μ k) * b.repr x j = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (hμ (sub_eq_zero.mp h)) hj
      · exact h
    rw [h0, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hj),
      smul_zero]

theorem comm_of_eigenbasis {L V κ : Type} [Field L] [AddCommGroup V] [Module L V]
    (b : Module.Basis κ L V) (μ : κ → L) (hμ : Function.Injective μ)
    (f g h : Module.End L V) (hf : ∀ k, f (b k) = μ k • b k) (hg : g ∘ₗ f = f ∘ₗ g)
    (hh : h ∘ₗ f = f ∘ₗ h) : g ∘ₗ h = h ∘ₗ g := by
  refine b.ext fun k => ?_
  obtain ⟨c, hc⟩ := apply_basis_eq_smul b μ hμ f g hf hg k
  obtain ⟨d, hd⟩ := apply_basis_eq_smul b μ hμ f h hf hh k
  simp only [LinearMap.comp_apply]
  rw [hd, map_smul, hc, map_smul, hd, smul_smul, smul_smul, mul_comm]

theorem comm_of_separable_algClosed {L ι : Type} [Field L] [IsAlgClosed L] [Fintype ι] [DecidableEq ι]
    (A G H : Matrix ι ι L) (hs : A.charpoly.Separable) (hG : G * A = A * G) (hH : H * A = A * H) :
    G * H = H * G := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  set f := Matrix.toLin' A with hfdef
  set s : Finset L := A.charpoly.roots.toFinset with hsdef
  have hcard : s.card = Fintype.card ι := by
    rw [hsdef, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
  have hev : ∀ μ : (s : Set L), Module.End.HasEigenvalue f μ := by
    intro μ
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hfdef, Matrix.charpoly_toLin']
    have hμ := μ.2
    simp only [Finset.mem_coe, hsdef, Multiset.mem_toFinset] at hμ
    exact Polynomial.isRoot_of_mem_roots hμ
  choose v hv using fun μ : (s : Set L) => (hev μ).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent f (s : Set L) v hv
  have hc : Fintype.card (s : Set L) = Module.finrank L (ι → L) := by
    simp [hcard]
  haveI : Nonempty (s : Set L) := by
    rw [← Fintype.card_pos_iff, hc, Module.finrank_fintype_fun_eq_card]; exact Fintype.card_pos
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have hb : ∀ k, f (b k) = (k : L) • b k := fun k => by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    exact (hv k).apply_eq_smul
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact comm_of_eigenbasis b (fun k => (k : L)) Subtype.coe_injective f _ _ hb
    (by rw [← Matrix.toLin'_mul, hG, Matrix.toLin'_mul])
    (by rw [← Matrix.toLin'_mul, hH, Matrix.toLin'_mul])

theorem centraliser_comm_of_separable : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (γ g h : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → g * γ = γ * g → h * γ = γ * h → g * h = h * g := by
  intro K _ ι _ _ γ g h hs hg hh
  apply Units.ext
  have hg' := congrArg Units.val hg
  have hh' := congrArg Units.val hh
  simp only [Units.val_mul] at hg' hh' ⊢
  let φ := algebraMap K (AlgebraicClosure K)
  apply Matrix.map_injective φ.injective
  simp only [Matrix.map_mul]
  apply comm_of_separable_algClosed ((γ : Matrix ι ι K).map φ)
  · rw [Matrix.charpoly_map]; exact hs.map
  · rw [← Matrix.map_mul, hg', Matrix.map_mul]
  · rw [← Matrix.map_mul, hh', Matrix.map_mul]

end GlobalTheory.CentSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKCentAf

theorem baseChange_centralizer_comm (K k B A : Type) [Field K] [CommRing k] [Algebra K k] [Ring B]
    [Algebra K B] [Ring A] [Algebra K A] (γ : B) (f : A →ₐ[K] B)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) :
    ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y ↔
      y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id k k) f) := by
  let ad : B →ₗ[K] B := LinearMap.mulRight K γ - LinearMap.mulLeft K γ
  have hex : Function.Exact f.toLinearMap ad := by
    intro x
    simp only [ad, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply]
    exact hcent x
  have hmap : ∀ y, Algebra.TensorProduct.map (AlgHom.id k k) f y = LinearMap.lTensor k f.toLinearMap y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have had : ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) - ((1 : k) ⊗ₜ[K] γ) * y = LinearMap.lTensor k ad y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      simp [ad, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add, ← hx, ← hy]; noncomm_ring
  have hex' := Module.Flat.lTensor_exact k hex
  intro y
  rw [← sub_eq_zero, had, hex' y]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, hmap z⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hmap z).symm⟩

theorem commute_of_centralizer (K k B A : Type) [Field K] [CommRing k] [Algebra K k] [Ring B]
    [Algebra K B] [CommRing A] [Algebra K A] (γ : B) (f : A →ₐ[K] B)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) (y z : k ⊗[K] B)
    (hy : y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y)
    (hz : z * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * z) : y * z = z * y := by
  obtain ⟨y', rfl⟩ := (baseChange_centralizer_comm K k B A γ f hcent y).1 hy
  obtain ⟨z', rfl⟩ := (baseChange_centralizer_comm K k B A γ f hcent z).1 hz
  rw [← map_mul, ← map_mul, mul_comm]

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem cent_iff_mem (P : Pair G) (y : G.C) :
    y * (P.γ : G.C) = (P.γ : G.C) * y ↔
      y ∈ Set.range ((Algebra.adjoin G.F ({(P.γ : G.C)} : Set G.C)).val.restrictScalars ℚ) := by
  have hcsa := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC (P.γ : G.C) P.reg.2 P.reg.1
  constructor
  · intro h
    have hy : y ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
      rw [Subalgebra.mem_centralizer_iff]
      simpa using h.symm
    rw [hcsa] at hy
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    have hw : (w : G.C) ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by rw [hcsa]; exact w.2
    rw [Subalgebra.mem_centralizer_iff] at hw
    exact (hw _ rfl).symm

theorem conj_commute (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t)
    (a : G.GAf) (ha : a ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self)) :
    (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) *
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
      ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) *
        (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) := by
  set U : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom P.γ with hU
  have hUv : (U : AfP p ⊗[ℚ] G.C) = (1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C) := rfl
  have hδ : ((P.toAf x t hx P.self : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = x * U * x⁻¹ := rfl
  have h1 := congrArg (fun g : G.GAf => (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1) ha
  simp only [Subgroup.coe_mul, Prod.fst_mul, MonoidHom.id_apply] at h1
  rw [hδ] at h1
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have h2 : x⁻¹ * A * x * U = U * (x⁻¹ * A * x) := by
    calc x⁻¹ * A * x * U = x⁻¹ * (A * (x * U * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * U * x⁻¹ * A) * x := by rw [h1]
      _ = U * (x⁻¹ * A * x) := by group
  rw [← hUv, ← Units.val_mul, ← Units.val_mul, h2]

theorem twCent_comm : ∀ {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
    ∀ a ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self),
    ∀ b ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self), a * b = b * a := by
  intro p _ G P x t hx a ha b hb
  have hc := commute_of_centralizer ℚ (AfP p) G.C _ (P.γ : G.C) _ (cent_iff_mem P) _ _
    (conj_commute P x t hx a ha) (conj_commute P x t hx b hb)
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  set B := (b : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have hc' : (x⁻¹ * A * x) * (x⁻¹ * B * x) = (x⁻¹ * B * x) * (x⁻¹ * A * x) := Units.ext (by
    simpa only [Units.val_mul] using hc)
  have hAB : A * B = B * A := by
    calc A * B = x * ((x⁻¹ * A * x) * (x⁻¹ * B * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * B * x) * (x⁻¹ * A * x)) * x⁻¹ := by rw [hc']
      _ = B * A := by group
  apply Subtype.ext
  apply Prod.ext
  · simpa only [Subgroup.coe_mul, Prod.fst_mul] using hAB
  · simp only [Subgroup.coe_mul, Prod.snd_mul]
    exact mul_comm _ _

end GlobalTheory.LKCentAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlaces
section
noncomputable section

open Matrix NumberField
open scoped TensorProduct Classical

namespace GlobalTheory.LKTrip.HTGroup

theorem span_real_embedding_places (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] :
    Submodule.span ℝ (Set.range fun (a : F) (v : InfinitePlace F) => v.embedding a) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top
  | exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top
  | (apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top ..)

variable {p : ℕ} [Fact p.Prime]

theorem psiR_tmul (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  simp only [psiR, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]
  rfl

theorem psiR_pi_bijective (G : HTGroup p) :
    Function.Bijective (fun x : ℝ ⊗[ℚ] G.C => fun v : InfinitePlace G.F => G.psiR v x) := by
  let Ψ : ℝ ⊗[ℚ] G.C →ₐ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := Pi.algHom ℝ _ fun v => G.psiR v
  have hΨ : ∀ x, Ψ x = fun v => G.psiR v x := fun x => rfl
  set S := Ψ.range with hS
  have hsc : ∀ a : G.F, Ψ (1 ⊗ₜ algebraMap G.F G.C a) =
      fun v : InfinitePlace G.F => Matrix.scalar (Fin G.n) (v.embedding a) := by
    intro a; funext v; rw [hΨ]; dsimp only; rw [psiR_tmul, one_smul, G.psi_F]
  let sc : (InfinitePlace G.F → ℂ) →ₗ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) :=
    { toFun := fun c v => Matrix.scalar (Fin G.n) (c v)
      map_add' := fun c d => by funext v; simp
      map_smul' := fun r c => by
        funext v
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Matrix.scalar_apply, Matrix.scalar_apply]
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, h] }
  have hscS : ∀ c : InfinitePlace G.F → ℂ, sc c ∈ S := by
    have htop := span_real_embedding_places G.F
    have hle : Submodule.span ℝ (Set.range fun (a : G.F) (v : InfinitePlace G.F) => v.embedding a) ≤
        (Subalgebra.toSubmodule S).comap sc := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_comap.2 ((AlgHom.mem_range _).2 ⟨_, hsc a⟩)
    intro c
    exact hle (htop ▸ Submodule.mem_top)
  have hsingle : ∀ (v₁ : InfinitePlace G.F) (m : Matrix (Fin G.n) (Fin G.n) ℂ), Pi.single v₁ m ∈ S := by
    intro v₁ m
    have hspan := GlobalTheory.UPel.HT.RealRepBij.span_range_eq_top v₁.embedding (G.psi v₁) G.rankC (G.psi_F v₁)
    have hm : m ∈ Submodule.span ℂ (Set.range (G.psi v₁)) := hspan ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have : (Pi.single v₁ (G.psi v₁ b) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) =
          sc (Pi.single v₁ 1) * Ψ (1 ⊗ₜ b) := by
        funext v
        rw [hΨ]
        by_cases h : v = v₁
        · subst h; simp [sc, psiR_tmul]
        · simp [sc, h, psiR_tmul]
      rw [this]; exact S.mul_mem (hscS _) ((AlgHom.mem_range _).2 ⟨_, rfl⟩)
    | zero => simpa using S.zero_mem
    | add x y _ _ hx hy => rw [Pi.single_add]; exact S.add_mem hx hy
    | smul z x _ hx =>
      have : (Pi.single v₁ (z • x) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) =
          sc (Pi.single v₁ z) * Pi.single v₁ x := by
        funext v
        by_cases h : v = v₁
        · subst h; simp [sc, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
        · simp [sc, h]
      rw [this]; exact S.mul_mem (hscS _) hx
  have hsurj : Function.Surjective Ψ := by
    intro y
    have : y ∈ S := by
      rw [← Finset.univ_sum_single y]
      exact Subalgebra.sum_mem _ fun v _ => hsingle v (y v)
    exact (AlgHom.mem_range _).1 this
  have hc : 2 * Fintype.card (InfinitePlace G.F) = Module.finrank ℚ G.F := by
    rw [← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero G.F]
    ring
  have hfin : Module.finrank ℝ (ℝ ⊗[ℚ] G.C) =
      Module.finrank ℝ (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    rw [← hc]; ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := Ψ.toLinearMap)).2 hsurj, hsurj⟩

end GlobalTheory.LKTrip.HTGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereMeanEqOfFrameNormEq
section
set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt MeasureTheory

namespace GlobalTheory.SphereMeanFrame

open GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure

def sphereHomeo {N : ℕ} (e : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1))) :
    UnitSphere N ≃ₜ UnitSphere N where
  toFun := sphereMap e
  invFun := sphereMap e.symm
  left_inv z := Subtype.ext (e.symm_apply_apply z.1)
  right_inv z := Subtype.ext (e.apply_symm_apply z.1)
  continuous_toFun := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _

set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in

theorem _root_.GlobalTheory.SphereMeanFrame.eval_linSubst {B N n : ℕ} (M : Matrix (Fin N) (Fin n) ℂ)
    (f : MvPolynomial (Fin B × Fin N) ℂ) (u : Fin B × Fin n → ℂ) :
    eval u (_root_.GlobalTheory.ChowHt.linSubst M f) =
      eval (fun p : Fin B × Fin N => ∑ k, M p.2 k * u (p.1, k)) f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  rw [_root_.ReciprocityTheory.MultiplicativeHeights.eval_aeval_alt]
  simp

set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in

theorem _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst {B N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hQ : ∀ x : EuclideanSpace ℂ (Fin (N + 1)), ‖Matrix.toEuclideanLin Q x‖ = ‖x‖)
    (f : MvPolynomial (Fin B × Fin (N + 1)) ℂ) :
    _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B (N + 1) (_root_.GlobalTheory.ChowHt.linSubst Q f) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B (N + 1) f := by
  let T : EuclideanSpace ℂ (Fin (N + 1)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { toLinearMap := Matrix.toEuclideanLin Q, norm_map' := hQ }
  let U := T.toLinearIsometryEquiv rfl
  let V : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { toLinearEquiv := U.toLinearEquiv.restrictScalars ℝ, norm_map' := U.norm_map }
  set μ : Measure (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) := Measure.pi fun _ => _root_.ReciprocityTheory.MultiplicativeHeights.sphereProb (N + 1) with hμ
  set Φ : (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) → (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) :=
    fun z b => _root_.ReciprocityTheory.MultiplicativeHeights.sphereMap V (z b) with hΦdef
  have hΦ : MeasurePreserving Φ μ μ := measurePreserving_pi _ _ (fun _ => _root_.ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereMap V)
  set g : (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) → ℝ := fun z => Real.log ‖eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) f‖ with hg
  have hcont : Continuous (fun z : Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1) => _root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) := by
    unfold _root_.ReciprocityTheory.MultiplicativeHeights.blockPoint
    exact continuous_pi fun p => (continuous_apply p.2).comp
      ((_root_.ReciprocityTheory.MultiplicativeHeights.continuous_spherePoint (N + 1)).comp (continuous_apply p.1))
  have hgm : Measurable g :=
    Real.measurable_log.comp (((MvPolynomial.continuous_eval f).comp hcont).norm.measurable)
  have hpt : ∀ z, eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) (_root_.GlobalTheory.ChowHt.linSubst Q f) = eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint (Φ z)) f := by
    intro z
    rw [_root_.GlobalTheory.SphereMeanFrame.eval_linSubst]
    congr 1
  change ∫ z, Real.log ‖eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) (_root_.GlobalTheory.ChowHt.linSubst Q f)‖ ∂μ = ∫ z, g z ∂μ
  simp_rw [hpt]
  change ∫ z, g (Φ z) ∂μ = ∫ z, g z ∂μ
  rw [← integral_map hΦ.measurable.aemeasurable hgm.aestronglyMeasurable, hΦ.map_eq]

set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in

theorem _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_eq_of_frameNorm_eq : ∀ (B N : ℕ) (A A' : Matrix (Fin N) (Fin N) ℂ),
    A.det ≠ 0 → A'.det ≠ 0 → (∀ z, _root_.GlobalTheory.ChowHt.frameNorm A z = _root_.GlobalTheory.ChowHt.frameNorm A' z) →
    ∀ f : MvPolynomial (Fin B × Fin N) ℂ,
      _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst A f) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst A' f) := by
  intro B N A A' hA hA' hn f
  cases N with
  | zero =>
    have hAA : A = A' := Subsingleton.elim _ _
    rw [hAA]
  | succ N =>
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have hA'u : IsUnit A'.det := isUnit_iff_ne_zero.mpr hA'
    have hAQ : A * (A⁻¹ * A') = A' := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ hAu, one_mul]
    have key : _root_.GlobalTheory.ChowHt.linSubst A' f =
        _root_.GlobalTheory.ChowHt.linSubst (A⁻¹ * A') (_root_.GlobalTheory.ChowHt.linSubst A f) := by
      rw [_root_.GlobalTheory.HeightUnique.linSubst_linSubst, hAQ]
    rw [key, _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst (A⁻¹ * A')]
    intro x
    have h1 := hn (A'.mulVec x.ofLp)
    simp only [_root_.GlobalTheory.ChowHt.frameNorm, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA'u,
      Matrix.one_mulVec] at h1
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    convert h1 using 4 with i
    rfl

end GlobalTheory.SphereMeanFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentative
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.RepresentativeL2

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {Γ : Subgroup G} [Countable Γ] {μ : Measure G} {𝓕 : Set G}

theorem meas_mk : Measurable (Quotient.mk (QuotientGroup.rightRel Γ)) := measurable_quotient_mk''

theorem ae_up [μ.IsMulLeftInvariant] (h : IsFundamentalDomain Γ 𝓕 μ) {p : Quotient (QuotientGroup.rightRel Γ) → Prop}
    (hp : ∀ᵐ q ∂((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))), p q) :
    ∀ᵐ x ∂μ, p (Quotient.mk _ x) := by
  have h1 := ae_of_ae_map (meas_mk (Γ := Γ)).aemeasurable hp
  rw [ae_iff, Measure.restrict_apply₀' h.nullMeasurableSet] at h1
  rw [ae_iff]
  refine h.measure_zero_of_invariant _ (fun g => ?_) h1
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have : (Quotient.mk (QuotientGroup.rightRel Γ) (g⁻¹ • x)) = Quotient.mk _ x := by
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    simp [Subgroup.smul_def]
  simp only [Set.mem_setOf_eq, this]

end General

theorem repr_properties : ∀ (D : D7) (V : HSp D), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → (∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ F, Repr V μ 𝓕 F φ) ∧ (∀ F ψ ψ', Continuous ψ → Continuous ψ' → Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F ψ' → ψ = ψ') ∧ (∀ F F' ψ, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ → F = F') ∧ (∀ F ψ g, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 (ρ g F) (rTr V g ψ)) ∧ (∀ F F' ψ ψ' (a : ℂ), Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → Repr V μ 𝓕 (a • F + F') (a • ψ + ψ')) ∧ ∀ F F' ψ ψ', Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → IntegrableOn (fun x => star (ψ x) * ψ' x) 𝓕 μ ∧ ⟪F, F'⟫_ℂ = ∫ x in 𝓕, star (ψ x) * ψ' x ∂μ := by
  intro D V μ 𝓕 ρ hp hr
  obtain ⟨-, -, -, hB, hT, -, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hp.haar
  haveI := hp.right
  have hm : Measurable (autMk V) := meas_mk
  haveI : IsFiniteMeasure (nuQ V μ 𝓕) := ⟨by
    rw [nuQ, Measure.map_apply hm MeasurableSet.univ]
    simpa [lt_top_iff_ne_top] using hp.fin⟩
  have up : ∀ {p : AutQ V → Prop}, (∀ᵐ q ∂(nuQ V μ 𝓕), p q) → ∀ᵐ x ∂μ, p (autMk V x) := fun h => ae_up hp.fd h
  refine ⟨fun φ hφ hinv ⟨C, hC⟩ => ?_, fun F ψ ψ' h h' e e' => ?_, fun F F' ψ e e' => ?_, fun F ψ g e => ?_,
    fun F F' ψ ψ' a e e' => ?_, fun F F' ψ ψ' e e' => ?_⟩
  · let f : AutQ V → ℂ := Quotient.lift φ fun a b hab => by
      have := hinv _ (QuotientGroup.rightRel_apply.1 hab) a
      rw [inv_mul_cancel_right] at this
      exact this.symm
    have hf : Measurable f := measurable_from_quotient.2 hφ.measurable
    have hL : MemLp f 2 (nuQ V μ 𝓕) :=
      MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun q => by
        induction q using Quotient.inductionOn with
        | h x => exact hC x)
    exact ⟨hL.toLp f, up hL.coeFn_toLp⟩
  · refine (h.ae_eq_iff_eq μ h').1 ?_
    filter_upwards [e, e'] with x h1 h2
    rw [← h1, h2]
  · refine Lp.ext ?_
    refine (ae_map_iff hm.aemeasurable
      ((Lp.stronglyMeasurable F).measurableSet_eq_fun (Lp.stronglyMeasurable F'))).2 (ae_restrict_of_ae ?_)
    filter_upwards [e, e'] with x h1 h2
    rw [h1, h2]
  · have e2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae e
    filter_upwards [hr.val g F, e2] with x h1 h2
    rw [h1, h2]; rfl
  · filter_upwards [up (Lp.coeFn_add (a • F) F'), up (Lp.coeFn_smul a F), e, e'] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]; rfl
  · have hI : Integrable (fun q => ⟪F q, F' q⟫_ℂ) (nuQ V μ 𝓕) := L2.integrable_inner F F'
    have hae : (fun x => ⟪F (autMk V x), F' (autMk V x)⟫_ℂ) =ᵐ[μ.restrict 𝓕] fun x => star (ψ x) * ψ' x := by
      refine ae_restrict_of_ae ?_
      filter_upwards [e, e'] with x h1 h2
      rw [h1, h2]
      simp [mul_comm]
    refine ⟨((integrable_map_measure hI.aestronglyMeasurable hm.aemeasurable).1 hI).congr hae, ?_⟩
    rw [L2.inner_def, ← integral_congr_ae hae]
    exact integral_map hm.aemeasurable hI.aestronglyMeasurable

end GlobalTheory.HolDict.RepresentativeL2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationModuleStatementStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_module_statement : GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule := by
  first | exact @GlobalTheory.PolarisationModuleProof.polarisationModule | exact GlobalTheory.PolarisationModuleProof.polarisationModule | (intros; apply GlobalTheory.PolarisationModuleProof.polarisationModule <;> assumption)
end

