import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerRankVanishing
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum
section
noncomputable section

namespace GlobalTheory.DeRhamSplit

open Module TensorProduct

section General

variable {F K L M : Type} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
  [AddCommGroup M] [Module L M] [Module F M] [IsScalarTower F L M]

def evalEmb (F K L : Type) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] :
    L ⊗[F] K →ₐ[L] ((K →ₐ[F] L) → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (AlgHom.pi fun τ => τ) fun _ _ => .all _ _

theorem evalEmb_tmul (a : L) (c : K) (τ : K →ₐ[F] L) :
    evalEmb F K L (a ⊗ₜ c) τ = a * τ c := by
  simp [evalEmb, Algebra.ofId_apply]

theorem evalEmb_bijective [FiniteDimensional F K]
    (hcard : Fintype.card (K →ₐ[F] L) = finrank F K) : Function.Bijective (evalEmb F K L) := by
  have hli : LinearIndependent L (fun τ : K →ₐ[F] L => (τ : K → L)) := by
    have h := (linearIndependent_monoidHom K L).comp (fun τ : K →ₐ[F] L => (τ : K →* L))
      (fun a b h => AlgHom.ext fun x => DFunLike.congr_fun h x)
    exact h
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hli
  have hsurj : Function.Surjective (evalEmb F K L).toLinearMap := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    refine ⟨1 ⊗ₜ c, ?_⟩
    funext τ
    simp [evalEmb_tmul, flip]
  have hfin : finrank L (L ⊗[F] K) = finrank L ((K →ₐ[F] L) → L) := by
    simp [hcard]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj, hsurj⟩

theorem finrank_eq_sum [FiniteDimensional F K]
    (hcard : Fintype.card (K →ₐ[F] L) = finrank F K) (m : K →ₐ[F] Module.End L M)
    (W : Submodule L M) [FiniteDimensional L W] (hW : ∀ c, ∀ x ∈ W, m c x ∈ W) :
    finrank L W = ∑ τ : K →ₐ[F] L,
      finrank L ↥(W ⊓ ⨅ c : K, LinearMap.ker (m c - τ c • LinearMap.id)) := by
  classical
  have hcomm : ∀ (a : L) (c : K), Commute (Algebra.ofId L (Module.End L M) a) (m c) :=
    fun a c => Algebra.commutes a (m c)
  let Ψ : L ⊗[F] K →ₐ[L] Module.End L M :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) m hcomm
  have hΨ : ∀ a c x, Ψ (a ⊗ₜ c) x = a • m c x := by
    intro a c x
    change (Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ c) : Module.End L M) x = _
    rw [Algebra.TensorProduct.lift_tmul]
    simp [Algebra.ofId_apply]
  let Φ := AlgEquiv.ofBijective _ (evalEmb_bijective hcard)
  let e : (K →ₐ[F] L) → L ⊗[F] K := fun τ => Φ.symm (Pi.single τ 1)
  have he : ∀ τ, evalEmb F K L (e τ) = Pi.single τ 1 := fun τ => Φ.apply_symm_apply _
  let E : (K →ₐ[F] L) → Submodule L M := fun τ => ⨅ c : K, LinearMap.ker (m c - τ c • LinearMap.id)
  have hE : ∀ τ x, x ∈ E τ ↔ ∀ c, m c x = τ c • x := by
    intro τ x
    simp [E, Submodule.mem_iInf, sub_eq_zero]
  have hΨW : ∀ z, ∀ x ∈ W, Ψ z x ∈ W := by
    intro z x hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ]; exact W.smul_mem _ (hW c x hx)
    | add y z hy hz => rw [map_add]; exact W.add_mem hy hz
  have hΨE : ∀ σ, ∀ x ∈ E σ, ∀ z, Ψ z x = evalEmb F K L z σ • x := by
    intro σ x hx z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ, evalEmb_tmul, (hE σ x).1 hx, mul_smul]
    | add y z hy hz => simp [map_add, hy, hz, add_smul]
  have hsum : ∑ τ, e τ = 1 := by
    apply (evalEmb_bijective hcard).1
    rw [map_sum, map_one]
    simp only [he]
    exact Finset.univ_sum_single (fun _ => (1 : L))
  have hmul : ∀ τ c, (1 ⊗ₜ c) * e τ = τ c • e τ := by
    intro τ c
    apply (evalEmb_bijective hcard).1
    rw [map_mul, map_smul, he]
    funext σ
    by_cases h : σ = τ
    · subst h; simp [evalEmb_tmul]
    · simp [Pi.single_eq_of_ne h]
  have hpE : ∀ τ x, Ψ (e τ) x ∈ E τ := by
    intro τ x
    rw [hE]
    intro c
    have := congrArg (fun z => Ψ z x) (hmul τ c)
    simpa [map_mul, map_smul, hΨ] using this
  let f : W →ₗ[L] (∀ τ, ↥(W ⊓ E τ)) := LinearMap.pi fun τ =>
    LinearMap.codRestrict _ ((Ψ (e τ)) ∘ₗ W.subtype) fun x => ⟨hΨW _ _ x.2, hpE τ _⟩
  have hf : ∀ x τ, (f x τ : M) = Ψ (e τ) x := fun _ _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have h1 : (x : M) = ∑ τ, Ψ (e τ) x := by
        rw [← LinearMap.sum_apply, ← map_sum, hsum, map_one]; rfl
      apply Subtype.ext
      rw [h1]
      simp [← hf, hx]
    · intro y
      refine ⟨⟨∑ σ, (y σ : M), W.sum_mem fun σ _ => (y σ).2.1⟩, ?_⟩
      funext τ
      apply Subtype.ext
      rw [hf, map_sum, Finset.sum_eq_single τ]
      · rw [hΨE τ _ (y τ).2.2, he]; simp
      · intro σ _ h
        rw [hΨE σ _ (y σ).2.2, he]; simp [Pi.single_eq_of_ne h]
      · simp
  have : ∀ τ, FiniteDimensional L ↥(W ⊓ E τ) := fun τ =>
    Submodule.finiteDimensional_of_le inf_le_left
  rw [(LinearEquiv.ofBijective f hbij).finrank_eq, Module.finrank_pi_fintype]

end General

section Period

open Formalism.WeaklyAdmissibleFiltrations

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mulVdR_tmul (c : K) (v : V) (b : BdR) :
    mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) c (v ⊗ₜ[Qp] b) =
      v ⊗ₜ[Qp] (algebraMap K BdR c * b) := by
  simp [mulVdR]

def mulHom (Qp K BdR LL V : Type) [Field Qp] [Field K] [Algebra Qp K] [CommRing BdR]
    [Algebra Qp BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [Field LL] [Algebra Qp LL]
    [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] :
    K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) where
  toFun c := mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) c
  map_one' := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul]
  map_mul' c d := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul, mul_assoc]
  map_zero' := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul]
  map_add' c d := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul, add_mul, tmul_add]
  commutes' a := by
    apply AlgebraTensorModule.ext
    intro v b
    rw [mulVdR_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul]
    simp [Algebra.algebraMap_eq_smul_one]

theorem act_mul (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (K := K) (LL := LL) c x) = mulVdR (K := K) (LL := LL) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, mulVdR_tmul]
  | add y z hy hz => simp [map_add, hy, hz]

theorem mul_mem_DdR (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) :
    mulVdR (K := K) (LL := LL) c x ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [act_mul, hx]

theorem mul_mem_FilV (a : ℤ) (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (K := K) (LL := LL) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    refine ⟨v ⊗ₜ ⟨c • b.1, (PD.Fil a).smul_mem c b.2⟩, ?_⟩
    simp [mulVdR_tmul, Algebra.smul_def]
  | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz

theorem finrank_DdR [FiniteDimensional Qp K] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    [FiniteDimensional LL ↥(DdR PD ρ)] (a : ℤ) :
    finrank LL ↥(DdR PD ρ) = ∑ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD ρ τ) ∧
    finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
      ∑ τ : K →ₐ[Qp] LL, finrank LL ↥(FildR PD ρ τ a) := by
  refine ⟨finrank_eq_sum hcard (mulHom Qp K BdR LL V) _ (mul_mem_DdR PD ρ), ?_⟩
  have : FiniteDimensional LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) :=
    Submodule.finiteDimensional_of_le inf_le_left
  rw [finrank_eq_sum hcard (mulHom Qp K BdR LL V) (DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)
    (fun c x hx => ⟨mul_mem_DdR PD ρ c x hx.1, mul_mem_FilV PD a c x hx.2⟩)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [inf_right_comm]
  rfl

theorem finrank_DdR_finsum [FiniteDimensional Qp K] (hcard : Nat.card (K →ₐ[Qp] LL) = finrank Qp K)
    [FiniteDimensional LL ↥(DdR PD ρ)] (a : ℤ) :
    finrank LL ↥(DdR PD ρ) = ∑ᶠ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD ρ τ) ∧
    finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
      ∑ᶠ τ : K →ₐ[Qp] LL, finrank LL ↥(FildR PD ρ τ a) := by
  rw [Nat.card_eq_fintype_card] at hcard
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact finrank_DdR PD ρ hcard a

end Period

open Formalism.BasicNotions in
theorem card_emb {l : ℕ} [Fact l.Prime] (K LL : Loc.FinExt l)
    (h : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1) :
    Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
  have := K.2
  rw [← AlgHom.card ℚ_[l] ↥K.1 (Loc.Om l), ← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective (fun τ => LL.1.val.comp τ) ⟨?_, ?_⟩
  · intro a b hab
    ext x
    exact DFunLike.congr_fun hab x
  · intro τ
    exact ⟨τ.codRestrict LL.1.toSubalgebra (h τ), by ext x; rfl⟩

open Formalism.BasicNotions Formalism.WeaklyAdmissibleFiltrations in
theorem finrank_DdR_local {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : Loc.FinExt l)
    (h : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1) {m : ℕ} (hm : 0 < m)
    (ρ : Representation ↥LL.1 ↥(Loc.GK K) (Fin m → ↥LL.1))
    (hρ : finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = finrank ℚ_[l] ↥K.1 * m) (a : ℤ) :
    finrank ↥LL.1 ↥(DdR (P.PD K) ρ) =
      ∑ᶠ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧
    finrank ↥LL.1 ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) a) =
      ∑ᶠ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ a) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hpos : 0 < finrank ↥LL.1 ↥(DdR (P.PD K) ρ) := by
    rw [hρ]
    exact Nat.mul_pos Module.finrank_pos hm
  have hD : FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) := FiniteDimensional.of_finrank_pos hpos
  have hc := card_emb _ _ h
  exact finrank_DdR_finsum (P.PD K) ρ hc a

end GlobalTheory.DeRhamSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricH1ZetaSubOneKills
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.TateGeo

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem cong_refl' (k : ℕ) (x : Ω) : Cong p k x x :=
  ⟨0, isIntegral_zero, by simp⟩

theorem cong_symm' {k : ℕ} {x y : Ω} (h : Cong p k x y) : Cong p k y x := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨-z, hz.neg, by rw [mul_neg, ← e]; ring⟩

theorem cong_trans' {k : ℕ} {x y w : Ω} (h1 : Cong p k x y) (h2 : Cong p k y w) : Cong p k x w := by
  obtain ⟨z, hz, e⟩ := h1
  obtain ⟨z', hz', e'⟩ := h2
  exact ⟨z + z', hz.add hz', by rw [mul_add, ← e, ← e']; ring⟩

theorem cong_add' {k : ℕ} {x y x' y' : Ω} (h1 : Cong p k x y) (h2 : Cong p k x' y') :
    Cong p k (x + x') (y + y') := by
  obtain ⟨z, hz, e⟩ := h1
  obtain ⟨z', hz', e'⟩ := h2
  exact ⟨z + z', hz.add hz', by rw [mul_add, ← e, ← e']; ring⟩

theorem cong_mul_left' {k : ℕ} {x y : Ω} (a : Ω) (ha : IsInt p a) (h : Cong p k x y) :
    Cong p k (a * x) (a * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨a * z, ha.mul hz, by rw [← mul_sub, e]; ring⟩

theorem cong_sum' {k : ℕ} {ι : Type*} (s : Finset ι) (f f' : ι → Ω)
    (h : ∀ i ∈ s, Cong p k (f i) (f' i)) : Cong p k (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cong_refl' (p := p) k (0 : Ω)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact cong_add' (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cong_of_eq' {k : ℕ} {x y : Ω} (h : x = y) : Cong p k x y := h ▸ cong_refl' k x

theorem mem_geoTop_iff (T : Tower p Ω) (g : Gal p Ω) :
    g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n ↔
      (∀ x : Ω, IsAlgZp p x → g x = x) ∧ ∀ n, g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := by
  rw [Subgroup.mem_inf, Subgroup.mem_iInf]
  refine and_congr Iff.rfl (forall_congr' fun n => ?_)
  rw [Gn, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  rfl

theorem exists_moved (T : Tower p Ω) {g : Gal p Ω} (hg : g ∉ Ggeo p Ω ⊓ ⨅ n, Gn T n) :
    ∃ a : Ω, g a ≠ a ∧ ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, h a = a := by
  rw [mem_geoTop_iff] at hg
  by_contra hno
  push_neg at hno
  apply hg
  refine ⟨fun x hx => ?_, fun n => ⟨?_, ?_⟩⟩
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno x hne
    exact hx' (((mem_geoTop_iff T h).mp hh).1 x hx)
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno _ hne
    exact hx' (((mem_geoTop_iff T h).mp hh).2 n).1
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno _ hne
    exact hx' (((mem_geoTop_iff T h).mp hh).2 n).2

theorem uniform_lc_on (hΩ : IsClo p Ω) (T : Tower p Ω) {k : ℕ} {c : Gal p Ω → Ω}
    (hc : IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c) :
    ∃ S₀ : Finset Ω, ∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n,
      (∀ x ∈ S₀, h x = g x) → Cong p k (c h) (c g) := by
  classical
  set H := Ggeo p Ω ⊓ ⨅ n, Gn T n with hH
  have hS : ∀ g : Gal p Ω, ∃ S : Finset Ω,
      (g ∈ H → ∀ h ∈ H, (∀ x ∈ S, h x = g x) → Cong p k (c h) (c g)) ∧
      (g ∉ H → ∀ h ∈ H, ¬ ∀ x ∈ S, h x = g x) := by
    intro g
    by_cases hg : g ∈ H
    · obtain ⟨S, hS⟩ := hc.2 g hg
      exact ⟨S, fun _ => hS, fun h => (h hg).elim⟩
    · obtain ⟨a, hga, ha⟩ := exists_moved T hg
      refine ⟨{a}, fun h => (hg h).elim, fun _ h hh hagree => ?_⟩
      have := hagree a (Finset.mem_singleton_self a)
      rw [ha h hh] at this
      exact hga this.symm
  choose S hS1 hS2 using hS
  obtain ⟨F, hF⟩ := GlobalTheory.T.finite_galois_approximation p Ω hΩ S
  refine ⟨F.biUnion S, fun g hg h hh hgh => ?_⟩
  obtain ⟨g0, hg0F, hg0⟩ := hF g
  have hg0H : g0 ∈ H := by
    by_contra hn
    exact hS2 g0 hn g hg hg0
  have h1 : Cong p k (c g) (c g0) := hS1 g0 hg0H g hg hg0
  have h2 : Cong p k (c h) (c g0) := hS1 g0 hg0H h hh (fun x hx => by
    rw [hgh x (Finset.mem_biUnion.mpr ⟨g0, hg0F, hx⟩), hg0 x hx])
  exact cong_trans' h2 (cong_symm' h1)

theorem uniform_lc_on_int (hΩ : IsClo p Ω) (T : Tower p Ω) {k : ℕ} {c : Gal p Ω → Ω}
    (hc : IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c) :
    ∃ S₁ : Finset Ω, (∀ s ∈ S₁, IsInt p s) ∧ ∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n,
      ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, (∀ x ∈ S₁, h x = g x) → Cong p k (c h) (c g) := by
  classical
  obtain ⟨S₀, hS₀⟩ := uniform_lc_on hΩ T hc
  have hm : ∀ x : Ω, ∃ a : O0 p, a ≠ 0 ∧ IsInt p (a • x) := fun x => by
    obtain ⟨a, ha, hi⟩ := (hΩ.alg.isAlgebraic x).exists_integral_multiple
    exact ⟨a, ha, hi⟩
  choose a ha hai using hm
  refine ⟨S₀.image (fun x => a x • x), ?_, fun g hg h hh hgh => hS₀ g hg h hh fun x hx => ?_⟩
  · intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    exact hai x
  · have e := hgh (a x • x) (Finset.mem_image_of_mem _ hx)
    rw [Algebra.smul_def, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at e
    have hne : algebraMap (O0 p) Ω (a x) ≠ 0 := by
      intro h0
      exact ha x (hΩ.inj (by rw [h0, map_zero]))
    exact mul_left_cancel₀ hne e

theorem h1_killed_by_zeta_sub_one_geo : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ c : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (c (g * h)) (c g + g (c h))) →
  Cob1 k (Ggeo p Ω ⊓ ⨅ n, Gn T n) (fun g => (T.ζ j - 1) * c g) := by
  intro p _ hp2 Ω _ _ hΩ T k j hj c hc hcoc
  classical
  set H := Ggeo p Ω ⊓ ⨅ n, Gn T n with hHdef
  obtain ⟨S₁, hS₁int, hS₁⟩ := uniform_lc_on_int hΩ T hc
  obtain ⟨y, E, hy, hEH, hu, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hΩ T H inf_le_right S₁ j hj
  set x : Ω := ∑ g ∈ E, g y * c g with hx
  have hxint : IsInt p x := by
    refine IsIntegral.sum _ fun g hg => ?_
    exact (IsIntegral.map g.toAlgHom hy).mul (hc.1 g (hEH g hg))
  refine ⟨-x, hxint.neg, fun h hh => ?_⟩
  have hσex : ∀ g ∈ E, ∃ g' ∈ E, (h * g) y = g' y ∧ ∀ s ∈ S₁, (h * g) s = g' s := fun g hg => by
    obtain ⟨g', ⟨hg'E, h1, h2⟩, -⟩ := hu (h * g) (H.mul_mem hh (hEH g hg))
    exact ⟨g', hg'E, h1, h2⟩
  choose! σ hσE hσy hσS using hσex
  have hσinj : Set.InjOn σ E := by
    intro g1 hg1 g2 hg2 he
    have ey : g1 y = g2 y := by
      have := (hσy g1 hg1).trans ((congrArg (fun f : Gal p Ω => f y) he).trans (hσy g2 hg2).symm)
      simpa using this
    have es : ∀ s ∈ S₁, g1 s = g2 s := fun s hs => by
      have := (hσS g1 hg1 s hs).trans ((congrArg (fun f : Gal p Ω => f s) he).trans (hσS g2 hg2 s hs).symm)
      simpa using this
    exact (hu g1 (hEH g1 hg1)).unique ⟨hg1, rfl, fun _ _ => rfl⟩ ⟨hg2, ey, es⟩
  have himg : E.image σ = E :=
    Finset.eq_of_subset_of_card_le (fun g' hg' => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hg'
      exact hσE g hg) (by rw [Finset.card_image_of_injOn hσinj])
  have hperm : ∑ g ∈ E, σ g y * c (σ g) = x := by
    rw [hx, ← Finset.sum_image (f := fun g' => g' y * c g') hσinj, himg]
  have hhx : h x = ∑ g ∈ E, h (g y) * h (c g) := by
    rw [hx, map_sum]; simp only [map_mul]
  have hζ : h (T.ζ j) = T.ζ j := (((mem_geoTop_iff T h).mp hh).2 j).1
  have hsumh : ∑ g ∈ E, h (g y) = T.ζ j - 1 := by
    rw [← map_sum, hsum, map_sub, map_one, hζ]
  have step : ∀ g ∈ E, Cong p k (h (g y) * h (c g)) (σ g y * c (σ g) - h (g y) * c h) := by
    intro g hg
    have hgH := hEH g hg
    have c1 : Cong p k (h (c g)) (c (h * g) - c h) := by
      obtain ⟨z, hz, e⟩ := hcoc h hh g hgH
      exact ⟨-z, hz.neg, by rw [mul_neg, ← e]; ring⟩
    have c2 : Cong p k (c (h * g)) (c (σ g)) :=
      hS₁ (σ g) (hEH _ (hσE g hg)) (h * g) (H.mul_mem hh hgH) (hσS g hg)
    have c3 : Cong p k (c (h * g) - c h) (c (σ g) - c h) := by
      obtain ⟨z, hz, e⟩ := c2
      exact ⟨z, hz, by rw [← e]; ring⟩
    have := cong_mul_left' (h (g y)) (IsIntegral.map h.toAlgHom (IsIntegral.map g.toAlgHom hy))
      (cong_trans' c1 c3)
    refine cong_trans' this (cong_of_eq' ?_)
    have ey : h (g y) = σ g y := by rw [← hσy g hg]; rfl
    rw [ey]; ring
  have total := cong_sum' E _ _ step
  rw [← hhx, Finset.sum_sub_distrib, hperm, ← Finset.sum_mul, hsumh] at total
  obtain ⟨z, hz, e⟩ := total
  refine ⟨z, hz, ?_⟩
  show (T.ζ j - 1) * c h - (h (-x) - -x) = _
  rw [map_neg, ← e]; ring

end GlobalTheory.K5.TateGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvd
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem To_MF : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → N ∣ L → q.Prime → ¬ q ∣ L →
    MF k L (ch ε) a → MF k L (ch ε) (To k (ch ε q) q a) := by
  intro k L N q ε a hk hNL hq hqL ha
  have h1 : ch ε 1 = 1 := by simp [ch]
  obtain ⟨hP, hqs⟩ := GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k q (ch ε) a hk hq.pos h1 ha.1
  refine ⟨hP, ?_⟩
  rw [hqs]
  refine GlobalTheory.T.heckeCharacterSlashSum_invariant_of_stable k L L N ε (DT L q) (Option (Fin q)) (repT q) (qs a) hk hNL hNL ?_ ?_
    (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator L q hq hqL) ha.2
  · rintro δ ⟨hdet, hL⟩
    refine ⟨by rw [hdet]; exact_mod_cast hq.pos, ?_⟩
    exact (Int.natCast_dvd_natCast.mpr hNL).trans hL
  · rintro δ ⟨hdet, hL⟩ γ hγ
    refine ⟨?_, ?_⟩
    · rw [Matrix.det_mul, hdet]
      simp
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hL _) (dvd_mul_of_dvd_right hγ _)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletion
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem dep_eq_sub (l : ℕ) (a : ℕ → ℂ) : dep l a = a + (-1 : ℂ) • Vo l (Uo l a) := by
  funext n
  simp only [dep, Vo, Uo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [Nat.mul_div_cancel' h]; ring
  · ring

theorem depletion_mf : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k L χ a → MF k L χ (Uo l a) ∧ MF k (L * l) χ (dep l a) := by
  intro k L l χ a hk hl hlL hχ ha
  have haL : MF k (L * l) χ a := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).2.2.2.2.1 (L * l) a (dvd_mul_right L l) ha)
  have hU : MF k L χ (Uo l a) := GlobalTheory.T.coeffHeckeUOperator_lowers_level k L l χ a hk hl hlL hχ haL
  refine ⟨hU, ?_⟩
  have hV : MF k (L * l) χ (Vo l (Uo l a)) := (GlobalTheory.T.coeffHeckeVOperator_raises_level k L l χ (Uo l a) hl.pos).1 hU
  have hV' := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (L * l) χ).2.2.1 (-1 : ℂ) _ hV).1
  rw [dep_eq_sub]
  exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (L * l) χ).2.1 _ _ haL hV').1

end GlobalTheory
end

