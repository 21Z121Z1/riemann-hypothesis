import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.IsGenEig

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FinD
section
namespace UpperTheory.V.Z.Sym.Tf

theorem finD {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V) (hB : B.Fin) (s : B.Tw)
    (f : G → ℂ) (hf : s.IsTest f) (g g' : G) :
    ∃ D : Finset Γ, ∀ δ, f (g⁻¹ * B.ι δ * s.θ g') ≠ 0 → ∃ d ∈ D, ∃ z ∈ B.Γ₀, δ = d * z := by
  classical
  set L : Subgroup Γ :=
    Subgroup.comap B.ι (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g')) B.U) with hL
  haveI hfi : (B.Γ₀.subgroupOf L).FiniteIndex := ⟨hB.stab g'⟩
  haveI : Finite (L ⧸ B.Γ₀.subgroupOf L) := Subgroup.finite_quotient_of_finiteIndex
  have hcomm' : ∀ γ, s.θ.symm (B.ι γ) = B.ι (s.θΓ.symm γ) := by
    intro γ
    apply s.θ.injective
    rw [MulEquiv.apply_symm_apply, s.comm, MulEquiv.apply_symm_apply]
  let T : Set Γ := {δ | f (g⁻¹ * B.ι δ * s.θ g') ≠ 0}
  let key : Γ → G ⧸ B.U := fun δ => (QuotientGroup.mk (s.θ.symm (g⁻¹ * B.ι δ * s.θ g')) : G ⧸ B.U)
  have hkey : ∀ δ ∈ T, key δ ∈ {x : G ⧸ B.U | f (s.θ (Quotient.out x)) ≠ 0} := by
    intro δ hδ
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U (s.θ.symm (g⁻¹ * B.ι δ * s.θ g'))
    show f (s.θ (Quotient.out (key δ))) ≠ 0
    have hu' : Quotient.out (key δ) = s.θ.symm (g⁻¹ * B.ι δ * s.θ g') * u := hu
    rw [hu', map_mul, MulEquiv.apply_symm_apply, hf.right]
    exact mul_ne_zero (Units.ne_zero _) hδ
  have himg : ((QuotientGroup.mk : Γ → Γ ⧸ B.Γ₀) '' T).Finite := by
    have hsub : T ⊆ ⋃ c ∈ {x : G ⧸ B.U | f (s.θ (Quotient.out x)) ≠ 0}, {δ | key δ = c} :=
      fun δ hδ => Set.mem_biUnion (hkey δ hδ) rfl
    refine Set.Finite.subset ?_ (Set.image_mono hsub)
    rw [Set.image_iUnion₂]
    refine hf.fin.biUnion fun c _ => ?_
    by_cases hne : ∃ δ₁, key δ₁ = c
    · obtain ⟨δ₁, hδ₁⟩ := hne
      let φ : L ⧸ B.Γ₀.subgroupOf L → Γ ⧸ B.Γ₀ :=
        fun q => ((δ₁ * s.θΓ ((Quotient.out q : L) : Γ) : Γ) : Γ ⧸ B.Γ₀)
      refine (Set.finite_range φ).subset ?_
      rintro _ ⟨δ, hδ, rfl⟩
      have hab := QuotientGroup.eq.mp (hδ₁.trans hδ.symm)
      have hl : s.θΓ.symm (δ₁⁻¹ * δ) ∈ L := by
        rw [hL, Subgroup.mem_comap, Subgroup.mem_map]
        refine ⟨_, hab, ?_⟩
        rw [← hcomm']
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
          MulEquiv.symm_apply_apply, mul_inv_rev, inv_inv]
        group
      obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (B.Γ₀.subgroupOf L)
        (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L)
      refine ⟨(QuotientGroup.mk (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L) : L ⧸ B.Γ₀.subgroupOf L), ?_⟩
      have hz0 : ((z : L) : Γ) ∈ B.Γ₀ := Subgroup.mem_subgroupOf.mp z.2
      show ((δ₁ * s.θΓ ((Quotient.out _ : L) : Γ) : Γ) : Γ ⧸ B.Γ₀) = _
      rw [show Quotient.out (QuotientGroup.mk (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L) :
          L ⧸ B.Γ₀.subgroupOf L) = _ from hz]
      rw [Subgroup.coe_mul, map_mul, MulEquiv.apply_symm_apply, s.fix _ hz0, ← mul_assoc,
        mul_inv_cancel_left]
      apply QuotientGroup.eq.mpr
      simpa using B.Γ₀.inv_mem hz0
    · refine Set.finite_empty.subset ?_
      rintro _ ⟨δ, hδ, rfl⟩
      exact (hne ⟨δ, hδ⟩).elim
  refine ⟨himg.toFinset.image (fun q => Quotient.out q), fun δ hδ => ?_⟩
  refine ⟨Quotient.out ((δ : Γ ⧸ B.Γ₀)), Finset.mem_image.mpr ⟨_, himg.mem_toFinset.mpr ⟨δ, hδ, rfl⟩, rfl⟩,
    (Quotient.out ((δ : Γ ⧸ B.Γ₀)))⁻¹ * δ, ?_, by group⟩
  exact QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

end UpperTheory.V.Z.Sym.Tf
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

open MulAction

def FormsFin : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : Base Γ G V), B.Fin →
    FiniteDimensional ℂ B.Forms

def RSpec : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V) (s : B.Tw) (f : G → ℂ), s.IsTest f →
    ∀ φ : B.Forms, (s.R f φ).1 = s.opF f φ.1

def RLin : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V) (s : B.Tw) (I : Type) (S : Finset I)
    (c : I → ℂ) (f : I → G → ℂ), (∀ i ∈ S, s.IsTest (f i)) →
    s.IsTest (fun y => ∑ i ∈ S, c i * f i y) ∧ s.R (fun y => ∑ i ∈ S, c i * f i y) = ∑ i ∈ S, c i • s.R (f i)

def RMul : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V) (s₁ s₂ : B.Tw) (f₁ f₂ : G → ℂ),
    s₁.IsTest f₁ → s₂.IsTest f₂ →
    (s₁.mul s₂).IsTest (s₁.conv f₁ f₂) ∧ s₁.R f₁ * s₂.R f₂ = (s₁.mul s₂).R (s₁.conv f₁ f₂)

def Trace : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : Base Γ G V), B.Fin →
    ∀ (s : B.Tw) (f : G → ℂ), s.IsTest f → ∀ (I : Type) (δ : I → Γ), (∀ i j, s.Rel (δ i) (δ j) → i = j) →
    (∀ γ : Γ, (∃ y, s.ker f γ y ≠ 0) → ∃ i, s.Rel (δ i) γ) →
    {i | ∃ y, s.ker f (δ i) y ≠ 0}.Finite ∧ LinearMap.trace ℂ B.Forms (s.R f) = ∑ᶠ i, s.term f (δ i)

def CentFin : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V), B.Fin →
    ∀ (s : B.Tw) (f : G → ℂ), s.IsTest f → ∀ δ : Γ, FinOrb (B.ι.comp (s.Cent δ).subtype) s.θ.toMonoidHom B.U f (B.ι δ)

def GqIndex : Prop :=
  ∀ (H' H G : Type) [Group H'] [Group H] [Group G] (φ : H' →* H) (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (k : G ⧸ U → ℂ),
    H₀.Normal → (∀ z ∈ H₀, ∀ y : G ⧸ U, j z • y = y) → (φ.range ⊔ H₀).index ≠ 0 → (∀ h y, k (j h • y) = k y) →
    (∃ S : Finset (G ⧸ U), ∀ y, k y ≠ 0 → ∃ h, ∃ x ∈ S, y = j h • x) →
    (∀ y : G ⧸ U, k y ≠ 0 → H₀.relIndex ((stabilizer G y).comap j) ≠ 0) →
    gqOn (j.comp φ) (H₀.comap φ) U k = ((φ.range ⊔ H₀).index : ℂ) * gqOn j H₀ U k

def GqMass : Prop :=
  ∀ (H T G : Type) [Group H] [CommGroup T] [Group G] (φ : H →* T) (ι : T →* G) (H₀ : Subgroup H) (C : Subgroup T) (θ : G →* G)
    (U : Subgroup G) (f : G → ℂ) (δ : G), (∀ u ∈ U, ∀ x, f (u⁻¹ * x * θ u) = f x) → (∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) →
    FinOrb ι θ U f δ → (∀ z ∈ H₀, ∀ y : G ⧸ U, ι (φ z) • y = y) → (φ.range ⊔ C).index ≠ 0 → H₀.relIndex (C.comap φ) ≠ 0 →
    (∀ y : G ⧸ U, f (y.out⁻¹ * δ * θ y.out) ≠ 0 →
      (stabilizer G y).comap ι ≤ C ∧ ((stabilizer G y).comap ι).relIndex C ≠ 0) → H₀ ≤ C.comap φ →
    gqOn (ι.comp φ) H₀ U (fun y => f (y.out⁻¹ * δ * θ y.out)) = mass φ H₀ C * orb ι C θ U f δ

def OrbProd : Prop :=
  ∀ (I G T : Type) [Group G] [CommGroup T] (Gv Tv : I → Type) [∀ v, Group (Gv v)] [∀ v, CommGroup (Tv v)]
    (K U : ∀ v, Subgroup (Gv v)) (C₀ C : ∀ v, Subgroup (Tv v)) (P : RPG G Gv K) (Q : RPG T Tv C₀)
    (ι : T →* G) (ιv : ∀ v, Tv v →* Gv v) (θ : G →* G) (θv : ∀ v, Gv v →* Gv v) (f : G → ℂ) (fv : ∀ v, Gv v → ℂ) (δ : G),
    (∀ v t, P.p v (ι t) = ιv v (Q.p v t)) → (∀ v g, P.p v (θ g) = θv v (P.p v g)) → (∀ g, f g = ∏ᶠ v, fv v (P.p v g)) →
    (∀ v, ∀ u ∈ U v, ∀ x, fv v (u⁻¹ * x * θv v u) = fv v x) → (∀ v t, (ιv v t)⁻¹ * P.p v δ * θv v (ιv v t) = P.p v δ) →
    ∀ S : Finset I, (∀ v ∈ S, FinOrb (ιv v) (θv v) (U v) (fv v) (P.p v δ)) →
    (∀ v ∉ S, K v ≤ U v ∧ C₀ v ≤ C v ∧ (C v).map (ιv v) ≤ U v ∧ fv v (P.p v δ) = 1 ∧
      ∀ y, fv v (y⁻¹ * P.p v δ * θv v y) ≠ 0 → ∃ t, ∃ u ∈ U v, y = ιv v t * u) →
    FinOrb ι θ (P.box U) f δ ∧
      orb ι (Q.box C) θ (P.box U) f δ = ∏ v ∈ S, orb (ιv v) (C v) (θv v) (U v) (fv v) (P.p v δ)

def OrbOne : Prop :=
  ∀ (T G : Type) [CommGroup T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G),
    (∀ u ∈ U, ∀ x, f (u⁻¹ * x * θ u) = f x) → (∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) → C.map ι ≤ U →
    (∀ y, f (y⁻¹ * δ * θ y) ≠ 0 → ∃ t, ∃ u ∈ U, y = ι t * u) → orb ι C θ U f δ = f δ

def OrbReps : Prop :=
  ∀ (T G : Type) [CommGroup T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G),
    (∀ u ∈ U, ∀ x, f (u⁻¹ * x * θ u) = f x) → (∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) → ∀ (J : Type) (S : Finset J) (x : J → G),
    (∀ i ∈ S, ∀ j ∈ S, ∀ t, ∀ u ∈ U, x j = ι t * x i * u → i = j) →
    (∀ y, f (y⁻¹ * δ * θ y) ≠ 0 → ∃ t, ∃ i ∈ S, ∃ u ∈ U, y = ι t * x i * u) →
    orb ι C θ U f δ = ∑ i ∈ S, (((stabilizer G (x i : G ⧸ U)).comap ι).relIndex C : ℂ) * f ((x i)⁻¹ * δ * θ (x i))

def OrbConj : Prop :=
  ∀ (T G : Type) [Group T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ x : G),
    (∀ u ∈ U, ∀ y, f (u⁻¹ * y * θ u) = f y) → (∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) → C.Normal →
    orb ((MulAut.conj x⁻¹).toMonoidHom.comp ι) C θ U f (x⁻¹ * δ * θ x) = orb ι C θ U f δ

def TrTheta : Prop :=
  ∀ (Λ M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (u : Λ → Module.End ℂ M) (Θ : Module.End ℂ M) (σ : Λ ≃ Λ),
    (∀ a b, Commute (u a) (u b)) → (∀ a, Θ * u a = u (σ a) * Θ) →
    ∃ (X : Finset (Λ → ℂ)) (c : (Λ → ℂ) → ℂ), (∀ χ ∈ X, IsGenEig u χ ∧ ∀ a, χ (σ a) = χ a) ∧
      ∀ a, LinearMap.trace ℂ M (u a * Θ) = ∑ χ ∈ X, c χ * χ a

def TrPos : Prop :=
  ∀ (Λ M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (u : Λ → Module.End ℂ M), (∀ a b, Commute (u a) (u b)) →
    ∃ (X : Finset (Λ → ℂ)) (d : (Λ → ℂ) → ℕ), (∀ χ, χ ∈ X ↔ IsGenEig u χ) ∧ (∀ χ ∈ X, 0 < d χ) ∧
      ∀ a, LinearMap.trace ℂ M (u a) = ∑ χ ∈ X, (d χ : ℂ) * χ a

def EigVec : Prop :=
  ∀ (Λ M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (u : Λ → Module.End ℂ M), (∀ a b, Commute (u a) (u b)) →
    ∀ χ, IsGenEig u χ ↔ ∃ v : M, v ≠ 0 ∧ ∀ a, u a v = χ a • v

def Extract : Prop :=
  ∀ (P I J : Type) [Mul P] (S : Finset I) (S' : Finset J) (a : I → ℂ) (b : J → ℂ) (α : I → P → ℂ) (β : J → P → ℂ),
    (∀ i ∈ S, ∀ p q, α i (p * q) = α i p * α i q) → (∀ j ∈ S', ∀ p q, β j (p * q) = β j p * β j q) →
    (∀ p, ∑ i ∈ S, a i * α i p = ∑ j ∈ S', b j * β j p) → ∀ χ : P → ℂ, χ ≠ 0 →
    (open Classical in ∑ j ∈ S'.filter (fun j => β j = χ), b j ≠ 0) → ∃ i ∈ S, a i ≠ 0 ∧ α i = χ

def Pigeon : Prop :=
  ∀ (X I : Type) (A : Set X), A.Finite → ∀ P : X → I → Prop, (∀ S : Finset I, ∃ x ∈ A, ∀ i ∈ S, P x i) → ∃ x ∈ A, ∀ i, P x i

end UpperTheory.V.Z.Sym.Tf
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceBlocks
section
open MulAction

namespace UpperTheory.V.Z.Sym.Tf

variable {Γ Y V : Type} [Group Γ] [MulAction Γ Y] [AddCommGroup V] [Module ℂ V]

theorem sum_fib {A B : Type} (m : A → B) (F : A → V) (F' : B → V) (c : B → ℕ) (hB : (Function.support F').Finite)
    (hc : ∀ b, F' b ≠ 0 → c b ≠ 0 ∧ Nat.card {a // m a = b} = c b) (hF : ∀ a, F a = (c (m a) : ℂ)⁻¹ • F' (m a)) :
    (Function.support F).Finite ∧ ∑ᶠ a, F a = ∑ᶠ b, F' b := by
  classical
  have hfibfin : ∀ b, F' b ≠ 0 → {a | m a = b}.Finite := by
    intro b hb
    have h1 := hc b hb
    have hne : Nat.card {a // m a = b} ≠ 0 := by rw [h1.2]; exact h1.1
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  have hsuppF : Function.support F ⊆ ⋃ b ∈ Function.support F', {a | m a = b} := by
    intro a ha
    refine Set.mem_iUnion₂.mpr ⟨m a, fun h0 => ha ?_, rfl⟩
    rw [hF, h0, smul_zero]
  have hfin : (Function.support F).Finite :=
    (hB.biUnion fun b hb => hfibfin b hb).subset hsuppF
  refine ⟨hfin, ?_⟩
  set s := hfin.toFinset with hs
  set T := hB.toFinset with hT
  rw [finsum_eq_sum_of_support_subset F (s := s) (by simp [s]),
    finsum_eq_sum_of_support_subset F' (s := T) (by simp [T])]
  have hmaps : ∀ a ∈ s, m a ∈ T := by
    intro a ha
    have ha' : F a ≠ 0 := by simpa [s] using ha
    have : F' (m a) ≠ 0 := fun h0 => ha' (by rw [hF, h0, smul_zero])
    simpa [T] using this
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun b hbT => ?_
  have hb' : F' b ≠ 0 := by simpa [T] using hbT
  obtain ⟨hcb, hcard⟩ := hc b hb'
  have hset : (↑(s.filter (fun a => m a = b)) : Set A) = {a | m a = b} := by
    ext a
    simp only [Finset.coe_filter, Set.mem_setOf_eq, s, Set.Finite.mem_toFinset, Function.mem_support]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [hF, h]
      exact smul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr hcb)) hb'
  have hcard' : (s.filter (fun a => m a = b)).card = c b := by
    rw [← Set.ncard_coe_finset, hset, ← Nat.card_coe_set_eq]
    exact hcard
  rw [Finset.sum_congr rfl (g := fun _ => (c b : ℂ)⁻¹ • F' b)]
  · rw [Finset.sum_const, hcard', ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hcb), one_smul]
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [hF, ha.2]

theorem rel_smul (Γ₀ : Subgroup Γ) [Γ₀.Normal] (g : Γ) (y : Y) :
    Γ₀.relIndex (stabilizer Γ (g • y)) = Γ₀.relIndex (stabilizer Γ y) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← Subgroup.Normal.map_conj_eq Γ₀ g]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem card_fib (H : Subgroup Γ) (b : orbitRel.Quotient H Y) :
    Nat.card {a : orbitRel.Quotient Γ Y × (Γ ⧸ H) // (Quotient.mk'' (a.2.out⁻¹ • a.1.out) : orbitRel.Quotient H Y) = b} =
      H.relIndex (stabilizer Γ b.out) := by
  classical
  set y0 := b.out with hy0
  set O0 : orbitRel.Quotient Γ Y := Quotient.mk'' y0 with hO0
  obtain ⟨t, ht⟩ : ∃ t : Γ, t • y0 = O0.out := by
    have h1 : (orbitRel Γ Y) O0.out y0 := Quotient.exact' (Quotient.out_eq' O0)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
    exact h1
  have hbq : (Quotient.mk'' y0 : orbitRel.Quotient H Y) = b := Quotient.out_eq' b
  have hinv : ∀ s : stabilizer Γ y0, (s : Γ)⁻¹ • y0 = y0 := fun s =>
    inv_smul_eq_iff.mpr (MulAction.mem_stabilizer_iff.mp s.2).symm
  have hmem : ∀ s : stabilizer Γ y0,
      (Quotient.mk'' ((((t * (s : Γ) : Γ) : Γ ⧸ H)).out⁻¹ • O0.out) : orbitRel.Quotient H Y) = b := by
    intro s
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (t * (s : Γ))
    rw [hh, ← ht, smul_smul]
    have e1 : (t * (s : Γ) * (h : Γ))⁻¹ * t = (h : Γ)⁻¹ * (s : Γ)⁻¹ := by group
    rw [e1, mul_smul, hinv s, ← hbq]
    exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨h⁻¹, rfl⟩))
  let Fib := {a : orbitRel.Quotient Γ Y × (Γ ⧸ H) //
    (Quotient.mk'' (a.2.out⁻¹ • a.1.out) : orbitRel.Quotient H Y) = b}
  let F : stabilizer Γ y0 → Fib := fun s => ⟨(O0, ((t * (s : Γ) : Γ) : Γ ⧸ H)), hmem s⟩
  have hF : ∀ s1 s2 : stabilizer Γ y0, F s1 = F s2 ↔ s1⁻¹ * s2 ∈ H.subgroupOf (stabilizer Γ y0) := by
    intro s1 s2
    rw [Subgroup.mem_subgroupOf]
    have e2 : (t * (s1 : Γ))⁻¹ * (t * (s2 : Γ)) = ((s1⁻¹ * s2 : stabilizer Γ y0) : Γ) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    constructor
    · intro h12
      have h3 : ((t * (s1 : Γ) : Γ) : Γ ⧸ H) = ((t * (s2 : Γ) : Γ) : Γ ⧸ H) :=
        congrArg (fun z : Fib => z.1.2) h12
      have h4 := QuotientGroup.eq.mp h3
      rw [e2] at h4
      exact h4
    · intro h12
      apply Subtype.ext
      refine Prod.ext rfl (QuotientGroup.eq.mpr ?_)
      show (t * (s1 : Γ))⁻¹ * (t * (s2 : Γ)) ∈ H
      rw [e2]
      exact h12
  have hsurj : Function.Surjective F := by
    rintro ⟨⟨O, q⟩, hq⟩
    obtain ⟨h, hh⟩ : ∃ h : H, (h : Γ) • y0 = q.out⁻¹ • O.out := by
      have h1 : (orbitRel H Y) (q.out⁻¹ • O.out) y0 := Quotient.exact' (hq.trans hbq.symm)
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
      exact h1
    have hO : O = O0 := by
      rw [← Quotient.out_eq' O]
      exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
        ⟨q.out * h, by rw [mul_smul, hh, smul_inv_smul]⟩))
    subst hO
    refine ⟨⟨t⁻¹ * q.out * h, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hh, smul_inv_smul, ← ht, inv_smul_smul]
    · apply Subtype.ext
      refine Prod.ext rfl ?_
      show ((t * (t⁻¹ * q.out * (h : Γ)) : Γ) : Γ ⧸ H) = q
      rw [show t * (t⁻¹ * q.out * (h : Γ)) = q.out * (h : Γ) by group,
        QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.out_eq']
  rw [Subgroup.relIndex, Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift F fun a b hab => (hF a b).mpr (QuotientGroup.leftRel_apply.mp hab)) ⟨?_, ?_⟩).symm
  · intro x y hxy
    induction x using Quotient.inductionOn'
    induction y using Quotient.inductionOn'
    exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr ((hF _ _).mp hxy))
  · intro z
    obtain ⟨s, rfl⟩ := hsurj z
    exact ⟨Quotient.mk'' s, rfl⟩

theorem countC (Γ₀ H : Subgroup Γ) [Γ₀.Normal] (h0 : ∀ z ∈ Γ₀, ∀ y : Y, z • y = y) (hH : Γ₀ ≤ H)
    (hs : ∀ y : Y, Γ₀.relIndex (stabilizer Γ y) ≠ 0) (k : Y → V) (hk : ∀ h ∈ H, ∀ y, k (h • y) = k y)
    (fin : {b : orbitRel.Quotient H Y | k b.out ≠ 0}.Finite) :
    (Function.support fun a : orbitRel.Quotient Γ Y × (Γ ⧸ H) =>
      (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out)).Finite ∧
    ∑ᶠ a : orbitRel.Quotient Γ Y × (Γ ⧸ H), (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out) =
      ∑ᶠ b : orbitRel.Quotient H Y, (Γ₀.relIndex (H ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out := by
  have hmul : ∀ y : Y, Γ₀.relIndex (H ⊓ stabilizer Γ y) * H.relIndex (stabilizer Γ y) =
      Γ₀.relIndex (stabilizer Γ y) := by
    intro y
    rw [Subgroup.relIndex_inf_mul_relIndex, inf_eq_left.mpr hH]
  have hcne : ∀ y : Y, H.relIndex (stabilizer Γ y) ≠ 0 := fun y h => hs y (by rw [← hmul y, h, mul_zero])
  let m : orbitRel.Quotient Γ Y × (Γ ⧸ H) → orbitRel.Quotient H Y :=
    fun a => Quotient.mk'' (a.2.out⁻¹ • a.1.out)
  have key : ∀ a : orbitRel.Quotient Γ Y × (Γ ⧸ H),
      (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out) =
      ((H.relIndex (stabilizer Γ (m a).out) : ℕ) : ℂ)⁻¹ •
        ((Γ₀.relIndex (H ⊓ stabilizer Γ (m a).out) : ℂ)⁻¹ • k (m a).out) := by
    intro a
    obtain ⟨h, hh⟩ : ∃ h : H, (h : Γ) • (a.2.out⁻¹ • a.1.out) = (m a).out := by
      have h1 : (orbitRel H Y) (m a).out (a.2.out⁻¹ • a.1.out) := Quotient.exact' (Quotient.out_eq' (m a))
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
      exact h1
    have hk' : k (m a).out = k (a.2.out⁻¹ • a.1.out) := by
      rw [← hh]
      exact hk h h.2 _
    have hidx : Γ₀.relIndex (stabilizer Γ (m a).out) = Γ₀.relIndex (stabilizer Γ a.1.out) := by
      rw [← hh, rel_smul, rel_smul]
    rw [smul_smul, ← mul_inv, ← Nat.cast_mul, mul_comm, hmul, hidx, hk']
  have hF'fin : (Function.support fun b : orbitRel.Quotient H Y =>
      (Γ₀.relIndex (H ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out).Finite := by
    refine fin.subset ?_
    intro b hb hkb
    exact hb (by simp only [hkb, smul_zero])
  exact sum_fib m
    (fun a => (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out))
    (fun b => (Γ₀.relIndex (H ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out)
    (fun b => H.relIndex (stabilizer Γ b.out)) hF'fin (fun b _ => ⟨hcne _, card_fib H b⟩) key

theorem finsum_sig {I : Type} {A : I → Type} (F : (Σ i, A i) → ℂ) (h : (Function.support F).Finite) :
    ∑ᶠ a, F a = ∑ᶠ i, ∑ᶠ x, F ⟨i, x⟩ := by
  classical
  set s := h.toFinset with hs
  let t := s.image Sigma.fst
  let u : ∀ i, Finset (A i) := fun i => s.preimage (Sigma.mk i) sigma_mk_injective.injOn
  have hsub : Function.support F ⊆ ↑(t.sigma u) := by
    intro a ha
    have ha' : a ∈ s := by simpa [s] using ha
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, t, u, Finset.mem_image,
      Finset.mem_preimage]
    exact ⟨⟨a, ha', rfl⟩, ha'⟩
  rw [finsum_eq_sum_of_support_subset F hsub, Finset.sum_sigma]
  rw [finsum_eq_sum_of_support_subset (s := t)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine (finsum_eq_sum_of_support_subset _ ?_).symm
    intro x hx
    simpa [u, s] using hx
  · intro i hi
    obtain ⟨x, hx⟩ : ∃ x, F ⟨i, x⟩ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hi (by simp [hc])
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨i, x⟩, by simpa [s] using hx, rfl⟩)

theorem trace_blocks {Q : Type} [Fintype Q] [FiniteDimensional ℂ V] (E : Q → Q → Module.End ℂ V) (L : Module.End ℂ (Q → V))
    (h : ∀ w o', L w o' = ∑ o, E o' o (w o)) : LinearMap.trace ℂ _ L = ∑ o, LinearMap.trace ℂ V (E o o) := by
  classical
  have hL : L = ∑ o', ∑ o, LinearMap.single ℂ (fun _ : Q => V) o' ∘ₗ (E o' o ∘ₗ LinearMap.proj o) := by
    refine LinearMap.ext fun w => funext fun p => ?_
    simp only [h, LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearMap.coe_single, Pi.single_apply]
    rw [Finset.sum_comm]
    simp
  rw [hL, map_sum]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [map_sum]
  have hterm : ∀ o, LinearMap.trace ℂ (Q → V)
      (LinearMap.single ℂ (fun _ : Q => V) o' ∘ₗ (E o' o ∘ₗ LinearMap.proj o)) =
      if o = o' then LinearMap.trace ℂ V (E o' o) else 0 := by
    intro o
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    split_ifs with hoo
    · subst hoo
      rw [LinearMap.proj_comp_single_same, LinearMap.comp_id]
    · rw [LinearMap.proj_comp_single_ne ℂ _ _ _ hoo, LinearMap.comp_zero, map_zero]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem finsum_triv (Γ₀ : Subgroup Γ) (h0 : ∀ z ∈ Γ₀, ∀ y : Y, z • y = y) (k : Y → V) (hk : (Function.support k).Finite) :
    {b : orbitRel.Quotient Γ₀ Y | k b.out ≠ 0}.Finite ∧
    ∑ᶠ b : orbitRel.Quotient Γ₀ Y, (Γ₀.relIndex (Γ₀ ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out = ∑ᶠ y, k y := by
  have hrel : ∀ y y' : Y, (orbitRel Γ₀ Y) y y' → y = y' := by
    intro y y' h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨g, hg⟩ := h
    rw [← hg, Subgroup.smul_def]
    exact h0 g g.2 y'
  let e : Y ≃ orbitRel.Quotient Γ₀ Y :=
    { toFun := fun y => Quotient.mk'' y
      invFun := fun b => b.out
      left_inv := fun y => hrel _ _ (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' y : orbitRel.Quotient Γ₀ Y)))
      right_inv := fun b => Quotient.out_eq' b }
  refine ⟨?_, ?_⟩
  · refine (hk.image e).subset ?_
    intro b hb
    exact ⟨b.out, hb, Quotient.out_eq' b⟩
  · have hcoef : ∀ b : orbitRel.Quotient Γ₀ Y, Γ₀.relIndex (Γ₀ ⊓ stabilizer Γ b.out) = 1 :=
      fun b => Subgroup.relIndex_eq_one.mpr inf_le_left
    simp only [hcoef, Nat.cast_one, inv_one, one_smul]
    exact finsum_comp_equiv e.symm (f := k)

end UpperTheory.V.Z.Sym.Tf
end

