import Mathlib

-- bundled from GroundTheory.AutomorphicForms.FiniteLengthLattice
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Function

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

def HasFiniteLength (ρ : Representation ℂ G V) : Prop :=
  IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule

variable {ρ : Representation ℂ G V}

theorem hasFiniteLength_iff :
    HasFiniteLength ρ ↔
      WellFoundedLT (Subrepresentation ρ) ∧ WellFoundedGT (Subrepresentation ρ) := by
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff', IsArtinian]
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨e.strictMono.wellFoundedLT, e.strictMono.wellFoundedGT⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e.symm.strictMono.wellFoundedGT, e.symm.strictMono.wellFoundedLT⟩

theorem HasFiniteLength.wellFoundedLT (h : HasFiniteLength ρ) :
    WellFoundedLT (Subrepresentation ρ) :=
  (hasFiniteLength_iff.1 h).1

theorem HasFiniteLength.wellFoundedGT (h : HasFiniteLength ρ) :
    WellFoundedGT (Subrepresentation ρ) :=
  (hasFiniteLength_iff.1 h).2

theorem hasFiniteLength_of_strictMono {ι : Type*} [Finite ι] {α : ι → Type*}
    [∀ i, PartialOrder (α i)] [∀ i, WellFoundedLT (α i)] [∀ i, WellFoundedGT (α i)]
    (Λ : Subrepresentation ρ → ∀ i, α i) (hΛ : StrictMono Λ) : HasFiniteLength ρ := by
  rw [hasFiniteLength_iff]
  refine ⟨hΛ.wellFoundedLT, ?_⟩
  have h1 : WellFoundedLT (∀ i, (α i)ᵒᵈ) := Pi.wellFoundedLT
  have h2 : WellFoundedGT (∀ i, α i) := ⟨h1.wf⟩
  exact hΛ.wellFoundedGT

theorem hasFiniteLength_of_subsingleton [Subsingleton V] : HasFiniteLength ρ := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton V)
  exact IsFiniteLength.of_subsingleton

theorem hasFiniteLength_of_isIrreducible [ρ.IsIrreducible] : HasFiniteLength ρ := by
  classical
  have : Finite (Subrepresentation ρ) := Finite.of_equiv _ IsSimpleOrder.equivBool.symm
  rw [hasFiniteLength_iff]
  exact ⟨Finite.to_wellFoundedLT, Finite.to_wellFoundedGT⟩

section MapComap

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}

def subrepMap (f : Representation.IntertwiningMap ρ σ) (A : Subrepresentation ρ) :
    Subrepresentation σ where
  toSubmodule := A.toSubmodule.map f.toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, A.apply_mem_toSubmodule g hx, Representation.IntertwiningMap.isIntertwining _ _ f g x⟩

def subrepComap (f : Representation.IntertwiningMap ρ σ) (B : Subrepresentation σ) :
    Subrepresentation ρ where
  toSubmodule := B.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule g x hx := by
    show f (ρ g x) ∈ B.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining]
    exact B.apply_mem_toSubmodule g hx

theorem subrepMap_mono (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepMap f) :=
  fun _ _ h _ ⟨x, hx, hxy⟩ => ⟨x, h hx, hxy⟩

theorem subrepComap_mono (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepComap f) :=
  fun _ _ h _ hx => h hx

theorem hasFiniteLength_of_injective (f : Representation.IntertwiningMap ρ σ)
    (hf : Injective f) (hσ : HasFiniteLength σ) : HasFiniteLength ρ := by
  have := hσ.wellFoundedLT
  have := hσ.wellFoundedGT
  refine hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation σ)
    (fun A _ => subrepMap f A) fun A B hAB => ?_
  refine lt_of_le_of_ne (fun _ => subrepMap_mono f hAB.le) fun h => hAB.ne ?_
  have h1 := congrFun h ()
  refine le_antisymm hAB.le fun x hx => ?_
  obtain ⟨y, hy, hyx⟩ : f x ∈ subrepMap f A := by
    show f x ∈ subrepMap f A
    rw [show subrepMap f A = subrepMap f B from h1]
    exact ⟨x, hx, rfl⟩
  rw [← hf hyx]
  exact hy

theorem hasFiniteLength_of_surjective (f : Representation.IntertwiningMap ρ σ)
    (hf : Surjective f) (hρ : HasFiniteLength ρ) : HasFiniteLength σ := by
  have := hρ.wellFoundedLT
  have := hρ.wellFoundedGT
  refine hasFiniteLength_of_strictMono (ι := Unit) (α := fun _ => Subrepresentation ρ)
    (fun B _ => subrepComap f B) fun A B hAB => ?_
  refine lt_of_le_of_ne (fun _ => subrepComap_mono f hAB.le) fun h => hAB.ne ?_
  have h1 := congrFun h ()
  refine le_antisymm hAB.le fun y hy => ?_
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ subrepComap f B := hy
  rw [← show subrepComap f A = subrepComap f B from h1] at hx
  exact hx

end MapComap

section Filtration

theorem hasFiniteLength_of_filtration {k : ℕ} (Vf : ℕ → Submodule ℂ V)
    (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ g)) (h0 : Vf 0 = ⊥) (hk : Vf k = ⊤)
    {W : Fin k → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (σ : ∀ j, Representation ℂ G (W j))
    (Ψ : ∀ j : Fin k, Representation.IntertwiningMap (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1)))
      (σ j))
    (hΨ : ∀ (j : Fin k) x, Ψ j x = 0 ↔ (x : V) ∈ Vf j) (hσ : ∀ j, HasFiniteLength (σ j)) :
    HasFiniteLength ρ := by
  classical
  have := fun j => (hσ j).wellFoundedLT
  have := fun j => (hσ j).wellFoundedGT

  let cut : ∀ j : Fin k, Subrepresentation ρ →
      Subrepresentation (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1))) := fun j A =>
    ⟨A.toSubmodule.comap (Vf (j + 1)).subtype, fun g x hx => A.apply_mem_toSubmodule g hx⟩
  refine hasFiniteLength_of_strictMono (α := fun j => Subrepresentation (σ j))
    (fun A j => subrepMap (Ψ j) (cut j A)) fun A B hAB => ?_
  have hmono' : ∀ j, subrepMap (Ψ j) (cut j A) ≤ subrepMap (Ψ j) (cut j B) := fun j =>
    subrepMap_mono _ (fun x hx => hAB.le hx)
  rw [Pi.lt_def]
  refine ⟨hmono', ?_⟩

  have hex : ∃ j, j < k ∧ ∃ x ∈ B, x ∈ Vf (j + 1) ∧ x ∉ A := by
    obtain ⟨x, hxB, hxA⟩ := SetLike.exists_of_lt hAB
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [h0] at hk
      exact hxA (by
        have : x ∈ (⊤ : Submodule ℂ V) := trivial
        rw [← hk] at this
        rw [(Submodule.mem_bot ℂ).1 this]
        exact A.toSubmodule.zero_mem)
    refine ⟨k - 1, by omega, x, hxB, ?_, hxA⟩
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0), hk]
    trivial
  let j₀ := Nat.find hex
  obtain ⟨hj₀k, x, hxB, hxV, hxA⟩ := Nat.find_spec hex
  have hbelow : ∀ y ∈ B, y ∈ Vf j₀ → y ∈ A := by
    intro y hyB hyV
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · rw [h, h0] at hyV
      rw [(Submodule.mem_bot ℂ).1 hyV]
      exact A.toSubmodule.zero_mem
    · by_contra hyA
      obtain ⟨m, hm⟩ : ∃ m, j₀ = m + 1 := ⟨j₀ - 1, by omega⟩
      have := Nat.find_min hex (m := m) (by omega)
      exact this ⟨by omega, y, hyB, by rw [← hm]; exact hyV, hyA⟩
  refine ⟨⟨j₀, hj₀k⟩, lt_of_le_of_ne (hmono' _) fun heq => hxA ?_⟩
  have hmem : Ψ ⟨j₀, hj₀k⟩ ⟨x, hxV⟩ ∈ subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ B) :=
    ⟨⟨x, hxV⟩, hxB, rfl⟩
  have heq' : subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ A) =
      subrepMap (Ψ ⟨j₀, hj₀k⟩) (cut ⟨j₀, hj₀k⟩ B) := heq
  rw [← heq'] at hmem
  obtain ⟨y, hyA, hyx⟩ := hmem
  have hyx' : Ψ ⟨j₀, hj₀k⟩ y = Ψ ⟨j₀, hj₀k⟩ ⟨x, hxV⟩ := hyx
  have hd : Ψ ⟨j₀, hj₀k⟩ (⟨x, hxV⟩ - y) = 0 := by rw [map_sub, hyx', sub_self]
  rw [hΨ] at hd
  have hyA' : (y : V) ∈ A := hyA
  have hdB : ((⟨x, hxV⟩ - y : Vf (j₀ + 1)) : V) ∈ B :=
    B.toSubmodule.sub_mem hxB (hAB.le hyA')
  have := hbelow _ hdB hd
  have hx' : x = ((⟨x, hxV⟩ - y : Vf (j₀ + 1)) : V) + y := by simp
  rw [hx']
  exact A.toSubmodule.add_mem this hyA'

end Filtration

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.GeometricLemmaOrbit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Topology Set DoubleCoset

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SigmaCompactSpace G]

section Action

variable (P Q : Subgroup G) (x : G)

@[instance_reducible]
def doubleCosetAction : MulAction (P × Q) (doubleCoset x (P : Set G) Q) where
  smul pq g := ⟨(pq.1 : G) * g * (pq.2 : G)⁻¹, by
    obtain ⟨p, hp, q, hq, h⟩ := mem_doubleCoset.1 g.2
    refine mem_doubleCoset.2 ⟨pq.1 * p, P.mul_mem pq.1.2 hp, q * (pq.2 : G)⁻¹,
      Q.mul_mem hq (Q.inv_mem pq.2.2), ?_⟩
    rw [h]
    group⟩
  one_smul g := Subtype.ext (by
    show ((1 : P × Q).1 : G) * g * ((1 : P × Q).2 : G)⁻¹ = g
    simp)
  mul_smul a b g := Subtype.ext (by
    show ((a * b).1 : G) * g * ((a * b).2 : G)⁻¹ =
      (a.1 : G) * ((b.1 : G) * g * (b.2 : G)⁻¹) * (a.2 : G)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]
    group)

end Action

variable {P Q : Subgroup G}

theorem isOpenMap_doubleCoset (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G)) (x : G)
    (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q)) :
    IsOpenMap (fun pq : P × Q => (⟨(pq.1 : G) * x * pq.2,
      mem_doubleCoset.2 ⟨pq.1, pq.1.2, pq.2, pq.2.2, rfl⟩⟩ : doubleCoset x (P : Set G) Q)) := by
  let := doubleCosetAction P Q x
  have : SigmaCompactSpace P := hP.sigmaCompactSpace
  have : SigmaCompactSpace Q := hQ.sigmaCompactSpace
  have : LocallyCompactSpace (doubleCoset x (P : Set G) Q) := hC.locallyCompactSpace
  have : ContinuousSMul (P × Q) (doubleCoset x (P : Set G) Q) := by
    refine ⟨Continuous.subtype_mk ?_ _⟩
    exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv)
  have : MulAction.IsPretransitive (P × Q) (doubleCoset x (P : Set G) Q) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨p₁, hp₁, q₁, hq₁, h₁⟩ := mem_doubleCoset.1 a.2
    obtain ⟨p₂, hp₂, q₂, hq₂, h₂⟩ := mem_doubleCoset.1 b.2
    refine ⟨(⟨p₂ * p₁⁻¹, P.mul_mem hp₂ (P.inv_mem hp₁)⟩, ⟨q₂⁻¹ * q₁, Q.mul_mem (Q.inv_mem hq₂) hq₁⟩), ?_⟩
    apply Subtype.ext
    show (p₂ * p₁⁻¹) * (a : G) * (q₂⁻¹ * q₁)⁻¹ = b
    rw [h₁, h₂]
    group
  have hopen := isOpenMap_smul_of_sigmaCompact (G := P × Q) (X := doubleCoset x (P : Set G) Q)
    ⟨x, mem_doubleCoset_self P Q x⟩
  let e : (P × Q) ≃ₜ (P × Q) := (Homeomorph.refl P).prodCongr (Homeomorph.inv Q)
  have : (fun pq : P × Q => (⟨(pq.1 : G) * x * pq.2,
      mem_doubleCoset.2 ⟨pq.1, pq.1.2, pq.2, pq.2.2, rfl⟩⟩ : doubleCoset x (P : Set G) Q)) =
      (fun γ : P × Q => γ • (⟨x, mem_doubleCoset_self P Q x⟩ : doubleCoset x (P : Set G) Q)) ∘ e := by
    funext pq
    apply Subtype.ext
    show (pq.1 : G) * x * pq.2 = (pq.1 : G) * x * ((pq.2⁻¹ : Q) : G)⁻¹
    simp
  rw [this]
  exact hopen.comp e.isOpenMap

theorem exists_nhds_inter_doubleCoset_subset (hP : IsClosed (P : Set G))
    (hQ : IsClosed (Q : Set G)) {x : G} (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q))
    {y : G} (hy : y ∈ doubleCoset x (P : Set G) Q) {UP UQ : Set G} (hUP : UP ∈ 𝓝 (1 : G))
    (hUQ : UQ ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 y, ∀ z ∈ V, z ∈ doubleCoset x (P : Set G) Q →
      ∃ p ∈ P, p ∈ UP ∧ ∃ q ∈ Q, q ∈ UQ ∧ z = p * y * q := by
  have hCy : doubleCoset y (P : Set G) Q = doubleCoset x (P : Set G) Q := doubleCoset_eq_of_mem hy
  rw [← hCy] at hC ⊢
  have hopen := isOpenMap_doubleCoset hP hQ y hC
  set W : Set (P × Q) := {pq | (pq.1 : G) ∈ interior UP ∧ (pq.2 : G) ∈ interior UQ}
  have hW : IsOpen W :=
    (isOpen_interior.preimage (continuous_subtype_val.comp continuous_fst)).inter
      (isOpen_interior.preimage (continuous_subtype_val.comp continuous_snd))
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (hopen W hW)
  have h1 : (1 : P × Q) ∈ W := ⟨mem_interior_iff_mem_nhds.2 hUP, mem_interior_iff_mem_nhds.2 hUQ⟩
  have hyV : y ∈ V := by
    have : (⟨y, mem_doubleCoset_self P Q y⟩ : doubleCoset y (P : Set G) Q) ∈
        Subtype.val ⁻¹' V := by
      rw [hV]
      exact ⟨1, h1, Subtype.ext (by simp)⟩
    exact this
  refine ⟨V, hVo.mem_nhds hyV, fun z hz hzC => ?_⟩
  have : (⟨z, hzC⟩ : doubleCoset y (P : Set G) Q) ∈ Subtype.val ⁻¹' V := hz
  rw [hV] at this
  obtain ⟨pq, hpq, hpqz⟩ := this
  refine ⟨pq.1, pq.1.2, interior_subset hpq.1, pq.2, pq.2.2, interior_subset hpq.2, ?_⟩
  exact (congrArg Subtype.val hpqz).symm

theorem exists_isCompact_subset_doubleCoset (hP : IsClosed (P : Set G))
    (hQ : IsClosed (Q : Set G)) {x : G} (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q))
    {Kc : Set G} (hK : IsCompact Kc) (hKC : Kc ⊆ doubleCoset x (P : Set G) Q) :
    ∃ L : Set G, IsCompact L ∧ L ⊆ Q ∧ ∀ z ∈ Kc, ∃ p ∈ P, ∃ l ∈ L, z = p * x * l := by
  obtain ⟨K₁, hK₁c, hK₁⟩ := exists_compact_mem_nhds (1 : G)
  have hloc : ∀ c ∈ Kc, ∃ V ∈ 𝓝 c, ∀ z ∈ V, z ∈ doubleCoset x (P : Set G) Q →
      ∃ p ∈ P, p ∈ (univ : Set G) ∧ ∃ q ∈ Q, q ∈ K₁ ∧ z = p * c * q :=
    fun c hc => exists_nhds_inter_doubleCoset_subset hP hQ hC (hKC hc) Filter.univ_mem hK₁
  choose V hV hVsub using hloc
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' V hV
  have hq : ∀ c : Kc, ∃ p ∈ P, ∃ q ∈ Q, (c : G) = p * x * q := fun c => mem_doubleCoset.1 (hKC c.2)
  choose pc hpc qc hqc hcq using hq
  refine ⟨⋃ c ∈ t, (fun z => qc c * z) '' ((Q : Set G) ∩ K₁), ?_, ?_, ?_⟩
  · exact t.isCompact_biUnion fun c _ =>
      (hK₁c.inter_left hQ).image (continuous_const.mul continuous_id)
  · intro l hl
    simp only [Set.mem_iUnion, Set.mem_image] at hl
    obtain ⟨c, _, z, hz, rfl⟩ := hl
    exact Q.mul_mem (hqc c) hz.1
  · intro z hz
    have hz' := ht hz
    simp only [Set.mem_iUnion] at hz'
    obtain ⟨c, hct, hzc⟩ := hz'
    obtain ⟨p, hp, -, q, hq, hqK, rfl⟩ := hVsub c c.2 z hzc (hKC hz)
    refine ⟨p * pc c, P.mul_mem hp (hpc c), qc c * q, ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_image]
      exact ⟨c, hct, q, ⟨hq, hqK⟩, rfl⟩
    · rw [hcq c]
      group

end Parabolic

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.LocallyProfinite
section
noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology MeasureTheory
open scoped Pointwise

section Space

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X]

theorem exists_isCompact_isOpen_subset {x : X} {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ V : Set X, IsCompact V ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds hU
  obtain ⟨V, hV, hxV, hVK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨V, hKc.of_isClosed_subset hV.isClosed hVK, hV.isOpen, hxV, hVK.trans hKU⟩

end Space

section VanDantzig

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem exists_openSubgroup_isCompact_subset {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨W, hWc, hWo, h1W, hWU⟩ := exists_isCompact_isOpen_subset hU
  obtain ⟨V, hV1, hWV⟩ := compact_open_separated_mul_right hWc hWo subset_rfl

  let H : Subgroup G :=
    { carrier := {x | ∀ w, w ∈ W ↔ w * x ∈ W}
      one_mem' := fun w => by simp
      mul_mem' := fun {a b} ha hb w => by rw [ha w, hb (w * a), mul_assoc]
      inv_mem' := fun {a} ha w => by
        have := ha (w * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  have hVH : V ∩ V⁻¹ ⊆ (H : Set G) := by
    rintro v ⟨hv, hv'⟩ w
    refine ⟨fun hw => hWV (Set.mul_mem_mul hw hv), fun hw => ?_⟩
    have := hWV (Set.mul_mem_mul hw (Set.mem_inv.1 hv'))
    rwa [mul_inv_cancel_right] at this
  have hHn : (H : Set G) ∈ 𝓝 (1 : G) :=
    mem_of_superset (inter_mem hV1 (inv_mem_nhds_one G hV1)) hVH
  have hHW : (H : Set G) ⊆ W := fun x hx => by
    have := (hx 1).1 h1W
    rwa [one_mul] at this
  let K : OpenSubgroup G := ⟨H, H.isOpen_of_mem_nhds hHn⟩
  exact ⟨K, hWc.of_isClosed_subset K.isClosed hHW, hHW.trans hWU⟩

theorem hasBasis_nhds_one_compactOpenSubgroup :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G => IsCompact (K : Set G))
      (fun K => (K : Set G)) :=
  ⟨fun _ => ⟨fun hU => exists_openSubgroup_isCompact_subset hU,
    fun ⟨K, _, hKU⟩ => mem_of_superset K.mem_nhds_one hKU⟩⟩

theorem hasBasis_nhds_compactOpenSubgroup (g : G) :
    (𝓝 g).HasBasis (fun K : OpenSubgroup G => IsCompact (K : Set G))
      (fun K => g • (K : Set G)) := by
  rw [← map_mul_left_nhds_one g]
  convert (hasBasis_nhds_one_compactOpenSubgroup (G := G)).map (g * ·) using 2 with K
  ext x
  simp only [Set.mem_smul_set, smul_eq_mul, Set.mem_image]

theorem exists_compactOpenSubgroup : ∃ K : OpenSubgroup G, IsCompact (K : Set G) := by
  obtain ⟨K, hK, -⟩ := exists_openSubgroup_isCompact_subset (univ_mem : univ ∈ 𝓝 (1 : G))
  exact ⟨K, hK⟩

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem isCompact_inf_left {K L : OpenSubgroup G} (hK : IsCompact (K : Set G)) :
    IsCompact ((K ⊓ L : OpenSubgroup G) : Set G) := by
  rw [OpenSubgroup.coe_inf]
  exact hK.inter_right L.isClosed

theorem exists_compactOpenSubgroup_normalized {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ N : OpenSubgroup G, IsCompact (N : Set G) ∧ (N : Set G) ⊆ U ∧
      ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
  obtain ⟨L, hLc, hLU⟩ := exists_openSubgroup_isCompact_subset hU

  have hopen : IsOpen ((fun p : G × G => p.1 * p.2 * p.1⁻¹) ⁻¹' (L : Set G)) :=
    L.isOpen.preimage (by fun_prop)
  have hsub : (K : Set G) ×ˢ ({1} : Set G) ⊆
      (fun p : G × G => p.1 * p.2 * p.1⁻¹) ⁻¹' (L : Set G) := by
    rintro ⟨k, x⟩ ⟨-, hx⟩
    simp only [mem_singleton_iff] at hx
    simp [hx]
  obtain ⟨u, v, -, hv, hKu, h1v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hopen hsub

  let N₀ : Subgroup G :=
    { carrier := {x | ∀ k ∈ K, k * x * k⁻¹ ∈ L}
      one_mem' := fun k _ => by simp
      mul_mem' := fun {a b} ha hb k hk => by
        have := mul_mem (ha k hk) (hb k hk)
        simpa [mul_assoc] using this
      inv_mem' := fun {a} ha k hk => by
        have := inv_mem (ha k hk)
        simpa [mul_assoc] using this }
  have hvN : v ⊆ (N₀ : Set G) := fun x hx k hk =>
    huv (show (k, x) ∈ u ×ˢ v from ⟨hKu hk, hx⟩)
  have hN₀n : (N₀ : Set G) ∈ 𝓝 (1 : G) := mem_of_superset (hv.mem_nhds (h1v rfl)) hvN
  have hN₀L : (N₀ : Set G) ⊆ L := fun x hx => by simpa using hx 1 K.one_mem
  let N : OpenSubgroup G := ⟨N₀, N₀.isOpen_of_mem_nhds hN₀n⟩
  refine ⟨N, hLc.of_isClosed_subset N.isClosed hN₀L, hN₀L.trans hLU, fun k hk n hn j hj => ?_⟩
  have := hn (j * k) (mul_mem hj hk)
  simpa [mul_assoc] using this

end VanDantzig

end GroundTheory.Automorphic
end
end

