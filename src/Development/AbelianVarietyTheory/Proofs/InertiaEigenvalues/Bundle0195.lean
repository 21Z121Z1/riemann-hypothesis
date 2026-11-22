import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0187
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemBreuilKisinLattice
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

theorem isoProj_mem_L : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), v ∈ P.L → GlobalTheory.CokerL.isoProj Δ c v ∈ P.L := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ P Δ c v hv
  letI := Fintype.ofFinite (rootsOfUnity e K)
  have key : ∀ s : ZMod a → K, (∀ τ, ‖s τ‖ ≤ 1) → ∀ w ∈ P.L, diagScale K a ι s w ∈ P.L := by
    intro s hs w hw
    have h : diagScale K a ι s w = (fun τ => C (s τ)) • w := by
      ext τ i
      simp [diagScale_apply, Pi.smul_apply', PowerSeries.smul_eq_C_mul]
    rw [h]
    refine P.smul_tot_mem_ext (fun τ => mem_A.2 fun n => ?_) hw
    rw [coeff_C]
    split_ifs
    · exact hs τ
    · simp
  have hnd : ¬ l ∣ e := by
    intro h
    have h1 : l ∣ e + 1 := by
      rw [TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a)]
      exact dvd_pow_self l (NeZero.ne a)
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h1))
  have he : ‖(e : K)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_natCast_eq l, Padic.norm_natCast_eq_one_iff.2
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd), inv_one]
  have hsc : isoProj Δ c v = diagScale K a ι (fun _ => (e : K)⁻¹) (∑ ζ : rootsOfUnity e K,
      diagScale K a ι (fun τ => ((TameGal.inertia ζ : TameGal K l e a).root τ)⁻¹ ^ c.val)
        (Δ.act (TameGal.inertia ζ) v)) := by
    simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  rw [hsc]
  refine key _ (fun _ => he) _ (Submodule.sum_mem _ fun ζ _ => key _ (fun τ => ?_) _ ?_)
  · rw [norm_pow, norm_inv, TameGal.norm_root, inv_one, one_pow]
  · exact Δ.act_mem_ext _ le_rfl rot_A hv

end GlobalTheory.CokerL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemIsotypicPartExplicit
section
noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

omit [NeZero e] in

theorem act_inertia_diagScale {P : PhiMod O K l e a ι} (Δ : Descent P) (ξ : rootsOfUnity e K)
    (s : ZMod a → K) (w : Vec K a ι) :
    Δ.act (TameGal.inertia ξ) (diagScale K a ι s w) =
      diagScale K a ι s (Δ.act (TameGal.inertia ξ) w) := by
  have h1 (u : Vec K a ι) : diagScale K a ι s u = (fun τ => (C (s τ) : K⟦X⟧)) • u := by
    ext τ i : 2
    simp [diagScale_apply, smul_eq_C_mul]
  have h2 : ringAct (TameGal.inertia ξ : TameGal K l e a) (fun τ => (C (s τ) : K⟦X⟧)) =
      fun τ => C (s τ) := by
    ext τ n
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero, coeff_rescale, coeff_C]
    split_ifs with h <;> simp [h]
  rw [h1, h1, Δ.act_smul_tot, h2]

theorem isoProj_mem_isotypic {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e)
    (v : Vec K a ι) : isoProj Δ c v ∈ Δ.isotypic c := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  unfold isoProj
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  intro ξ τ
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, act_inertia_diagScale,
    Finset.sum_apply, diagScale_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ξ) _ _ fun ζ => ?_
  rw [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, ← map_mul, smul_smul]
  congr 1
  rw [map_mul, TameGal.root_mul, TameGal.shift_inertia, sub_zero, ← mul_pow, mul_inv,
    mul_inv_cancel_left₀ (TameGal.root_ne_zero _ _)]

theorem isoProj_mem_isotypic' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι)
    (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δ c v => isoProj_mem_isotypic Δ c v

end GlobalTheory.CokerL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticePowSmulNhdsZeroBasis
section
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory

open Filter Topology in
open scoped TensorProduct in

theorem _root_.GlobalTheory.lattice_multiples_nhds_basis :
    ∀ (LL O V : Type) [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V] (T : Submodule O V) (lam : O), T.FG → Submodule.span LL (T : Set V) = ⊤ → IsOpen (Set.range (algebraMap O LL)) → algebraMap O LL lam ≠ 0 → (∀ U ∈ 𝓝 (0 : LL), ∃ a : ℕ, ∀ x : O, algebraMap O LL (lam ^ a * x) ∈ U) → (∀ a : ℕ, {v : V | ∃ t ∈ T, v = lam ^ a • t} ∈ 𝓝 (0 : V)) ∧ ∀ U ∈ 𝓝 (0 : V), ∃ a : ℕ, ∀ t ∈ T, lam ^ a • t ∈ U := by
  intro LL O V _ _ _ _ _ _ _ _ _ _ _ T lam hT hspan hopen hlam hsmall
  obtain ⟨n, s, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hT
  set φ : (Fin n → LL) →ₗ[LL] V := Fintype.linearCombination LL s with hφ
  have key : ∀ (a : ℕ) (c : Fin n → O),
      φ (fun i => algebraMap O LL (lam ^ a * c i)) = lam ^ a • ∑ i, c i • s i := by
    intro a c
    simp only [hφ, Fintype.linearCombination_apply, Finset.smul_sum, map_mul, mul_smul,
      algebraMap_smul]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    intro t ht
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp ht
    exact ⟨_, by rw [key 0 c, pow_zero, one_smul]⟩
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hsurj
  refine ⟨fun a => ?_, fun U hU => ?_⟩
  · have hc : algebraMap O LL (lam ^ a) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hlam
    set W : Set LL := Set.range fun x : O => algebraMap O LL (lam ^ a * x) with hW
    have hWeq : W = (Homeomorph.mulLeft₀ _ hc) '' Set.range (algebraMap O LL) := by
      ext y; simp [hW, map_mul]
    have hWo : IsOpen W := hWeq ▸ (Homeomorph.mulLeft₀ _ hc).isOpenMap _ hopen
    have hPo : IsOpen (φ '' Set.univ.pi fun _ => W) :=
      hq.isOpenMap _ (isOpen_set_pi Set.finite_univ fun _ _ => hWo)
    refine mem_of_superset (hPo.mem_nhds ⟨0, fun i _ => ⟨0, by simp⟩, map_zero φ⟩) ?_
    rintro v ⟨y, hy, rfl⟩
    choose c hc' using fun i => hy i (Set.mem_univ i)
    have : y = fun i => algebraMap O LL (lam ^ a * c i) := funext fun i => (hc' i).symm
    subst this
    exact ⟨_, (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨c, rfl⟩, key a c⟩
  · have h0 : φ ⁻¹' U ∈ 𝓝 (0 : Fin n → LL) :=
      hq.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
    rw [nhds_pi, Filter.mem_pi'] at h0
    obtain ⟨I, t, ht, hsub⟩ := h0
    obtain ⟨a, ha⟩ := hsmall (⋂ i, t i) (Filter.iInter_mem.mpr ht)
    refine ⟨a, fun v hv => ?_⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hv
    rw [← key a c]
    exact hsub fun i _ => Set.mem_iInter.mp (ha (c i)) i

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeTwistExactSequenceCohomology
section
noncomputable section

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.TensIsoExt

open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)

section Abstract

variable {O G : Type} [CommRing O] [Group G]
variable {A B C : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
  [AddCommGroup C] [Module O C]

def ambMap {π : Representation O G A} {π' : Representation O G B} (f : A →ₗ[O] B)
    (hf : ∀ g m, f (π g m) = π' g (f m)) : Amb π →ₗ[O] Amb π' :=
  Submodule.mapQ _ _ (f.compLeft G) (by
    rintro z ⟨b, -, hb⟩
    refine ⟨f b, Submodule.mem_top, ?_⟩
    funext g
    have h1 : π g b - b = z g := congrFun hb g
    change π' g (f b) - f b = f (z g)
    rw [← h1, map_sub, hf])

theorem ambMap_mk {π : Representation O G A} {π' : Representation O G B} (f : A →ₗ[O] B)
    (hf : ∀ g m, f (π g m) = π' g (f m)) (u : G → A) :
    ambMap f hf (Submodule.Quotient.mk u) = Submodule.Quotient.mk (fun g => f (u g)) := rfl

theorem amb_eq_iff {π : Representation O G A} (u v : G → A) :
    (Submodule.Quotient.mk u : Amb π) = Submodule.Quotient.mk v ↔ ∃ m, ∀ g, π g m - m = u g - v g := by
  rw [Submodule.Quotient.eq, ReciprocityTheory.Def.B1, Submodule.mem_map]
  constructor
  · rintro ⟨m, -, hm⟩
    exact ⟨m, fun g => congrFun hm g⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Submodule.mem_top, funext hm⟩

variable [TopologicalSpace G]

theorem mem_range_toAmb {π : Representation O G A} (x : Amb π) :
    x ∈ LinearMap.range (toAmb π) ↔ ∃ z ∈ Z1 π ⊤, Submodule.Quotient.mk z = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Submodule.Quotient.mk ⟨z, hz⟩, rfl⟩

theorem mem_cocycles_units_iff {π : Representation O G A} (z : G → A) :
    z ∈ Z1 π ⊤ ↔ IsLocallyConstant z ∧ ∀ g h, π g (z h) - z (g * h) + z g = 0 := by
  rw [Z1, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨hc, hd⟩
    exact ⟨hc.1, fun g h => congrFun hd (g, h)⟩
  · rintro ⟨hlc, hd⟩
    refine ⟨⟨hlc, fun _ => Submodule.mem_top⟩, ?_⟩
    funext x
    exact hd x.1 x.2

variable {HA HB HC : Type} [AddCommGroup HA] [Module O HA] [AddCommGroup HB] [Module O HB]
  [AddCommGroup HC] [Module O HC]

private theorem ambMap_injective_lemma {πA : Representation O G A} {πB : Representation O G B}
    {πC : Representation O G C} (α : A →ₗ[O] B) (β : B →ₗ[O] C) (hα : ∀ g m, α (πA g m) = πB g (α m))
    (hβ : ∀ g m, β (πB g m) = πC g (β m)) (αinj : Function.Injective α) (ex : Function.Exact α β)
    (hinv : πC.invariants = ⊥) : Function.Injective (ambMap α hα) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : (Submodule.Quotient.mk (fun g => α (u g)) : Amb πB) = Submodule.Quotient.mk 0 := by
    rw [Submodule.Quotient.mk_zero, ← hx, ambMap_mk]
  obtain ⟨m, hm⟩ := (amb_eq_iff _ _).1 h0
  have hm' : ∀ g, πB g m - m = α (u g) := fun g => by simpa using hm g
  have hfix : β m ∈ πC.invariants := by
    rw [Representation.mem_invariants]
    intro g
    have e := congrArg β (hm' g)
    rw [map_sub, hβ, ex.apply_apply_eq_zero] at e
    exact sub_eq_zero.1 e
  rw [hinv, Submodule.mem_bot] at hfix
  obtain ⟨a₀, ha₀⟩ := (ex m).1 hfix
  rw [← Submodule.Quotient.mk_zero, amb_eq_iff]
  refine ⟨a₀, fun g => αinj ?_⟩
  rw [map_sub, hα, ha₀, hm' g, Pi.zero_apply, sub_zero]

theorem five {πA : Representation O G A} {πB : Representation O G B} {πC : Representation O G C}
    (α : A →ₗ[O] B) (β : B →ₗ[O] C) (hα : ∀ g m, α (πA g m) = πB g (α m))
    (hβ : ∀ g m, β (πB g m) = πC g (β m)) (αinj : Function.Injective α) (ex : Function.Exact α β)
    (βsurj : Function.Surjective β)
    (a : HA →ₗ[O] HB) (b : HB →ₗ[O] HC) (ex' : Function.Exact a b) (bsurj : Function.Surjective b)
    (φA : HA →ₗ[O] Amb πA) (φB : HB →ₗ[O] Amb πB) (φC : HC →ₗ[O] Amb πC)
    (sqa : ∀ y, ambMap α hα (φA y) = φB (a y)) (sqb : ∀ y, ambMap β hβ (φB y) = φC (b y))
    (hle : LinearMap.range φB ≤ LinearMap.range (toAmb πB))
    (hlc : ∀ m, IsLocallyConstant fun g => πB g m) (hinv : πC.invariants = ⊥)
    (hA : Function.Injective φA ∧ LinearMap.range φA = LinearMap.range (toAmb πA))
    (hC : Function.Injective φC ∧ LinearMap.range φC = LinearMap.range (toAmb πC)) :
    Function.Injective φB ∧ LinearMap.range φB = LinearMap.range (toAmb πB) := by
  have hαi := ambMap_injective_lemma α β hα hβ αinj ex hinv
  refine ⟨?_, le_antisymm hle ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : φC (b y) = 0 := by rw [← sqb, hy, map_zero]
    have h2 : b y = 0 := hC.1 (by rw [h1, map_zero])
    obtain ⟨x, rfl⟩ := (ex' y).1 h2
    have h3 : φA x = 0 := hαi (by rw [sqa, hy, map_zero])
    have h4 : x = 0 := hA.1 (by rw [h3, map_zero])
    rw [h4, map_zero]
  · rintro _ ⟨ζ, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ζ
    obtain ⟨hzlc, hzc⟩ := (mem_cocycles_units_iff (z : G → B)).1 z.2
    have hβz : (fun g => β ((z : G → B) g)) ∈ Z1 πC ⊤ := by
      refine (mem_cocycles_units_iff _).2 ⟨hzlc.comp β, fun g h => ?_⟩
      rw [← hβ, ← map_sub, ← map_add, hzc g h, map_zero]
    have hC' := (mem_range_toAmb (Submodule.Quotient.mk (fun g => β ((z : G → B) g)) : Amb πC)).2
      ⟨_, hβz, rfl⟩
    rw [← hC.2] at hC'
    obtain ⟨w, hw⟩ := hC'
    obtain ⟨y, rfl⟩ := bsurj w
    obtain ⟨z', hz'mem, hz'eq⟩ := (mem_range_toAmb (φB y)).1 (hle (LinearMap.mem_range_self φB y))
    obtain ⟨hz'lc, hz'c⟩ := (mem_cocycles_units_iff z').1 hz'mem
    have hcl : (Submodule.Quotient.mk (fun g => β (z' g)) : Amb πC) =
        Submodule.Quotient.mk (fun g => β ((z : G → B) g)) := by
      rw [← ambMap_mk β hβ, hz'eq, sqb, hw]
    obtain ⟨c, hc⟩ := (amb_eq_iff _ _).1 hcl
    obtain ⟨m₀, hm₀⟩ := βsurj c
    have hk : ∀ g, β ((z : G → B) g - z' g + (πB g m₀ - m₀)) = 0 := by
      intro g
      have e := hc g
      rw [map_add, map_sub, map_sub, hβ, hm₀, e]
      abel
    choose u hu using fun g => (ex ((z : G → B) g - z' g + (πB g m₀ - m₀))).1 (hk g)
    have hulc : IsLocallyConstant u := by
      refine IsLocallyConstant.desc u α ?_ αinj
      have e : α ∘ u = fun g => (z : G → B) g - z' g + (πB g m₀ - m₀) := funext hu
      rw [e]
      exact (hzlc.sub hz'lc).add ((hlc m₀).sub (IsLocallyConstant.const m₀))
    have hum : u ∈ Z1 πA ⊤ := by
      refine (mem_cocycles_units_iff u).2 ⟨hulc, fun g h => αinj ?_⟩
      have e1 : (z : G → B) (g * h) = πB g ((z : G → B) h) + (z : G → B) g := by
        have e := hzc g h
        rw [sub_add_eq_add_sub, sub_eq_zero] at e
        exact e.symm
      have e2 : z' (g * h) = πB g (z' h) + z' g := by
        have e := hz'c g h
        rw [sub_add_eq_add_sub, sub_eq_zero] at e
        exact e.symm
      rw [map_zero, map_add, map_sub, hα, hu, hu, hu, e1, e2, map_mul, Module.End.mul_apply]
      simp only [map_add, map_sub]
      abel
    obtain ⟨x, hx⟩ : Submodule.Quotient.mk u ∈ LinearMap.range φA := by
      rw [hA.2]
      exact (mem_range_toAmb _).2 ⟨u, hum, rfl⟩
    refine ⟨y + a x, ?_⟩
    rw [map_add, ← sqa, hx, ambMap_mk, ← hz'eq, ← Submodule.Quotient.mk_add]
    change _ = (Submodule.Quotient.mk (z : G → B) : Amb πB)
    rw [amb_eq_iff]
    refine ⟨m₀, fun g => ?_⟩
    rw [Pi.add_apply, hu]
    abel

end Abstract
section Tens

variable {G LL O V : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousConstSMul LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (χ : G →* Oˣ)
  {X X' : Type} [AddCommGroup X] [Module O X] [AddCommGroup X'] [Module O X']

omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] in

theorem lTensor_equivariant (f : X →ₗ[O] X') (g : G) (m : ↥L.T ⊗[O] X) :
    f.lTensor ↥L.T (twCoef (latRep L) χ X g m) = twCoef (latRep L) χ X' g (f.lTensor ↥L.T m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul t x => simp only [twCoef, coefRep_tmul, LinearMap.lTensor_tmul]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem tensAmb_natural (f : X →ₗ[O] X') (y : H1tw L χ ⊗[O] X) :
    ambMap (f.lTensor ↥L.T) (lTensor_equivariant L χ f) (tensAmb L χ X y) =
      tensAmb L χ X' (f.lTensor (H1tw L χ) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [LinearMap.lTensor_tmul, tensAmb_tmul, tensAmb_tmul, ambMap_mk]
    congr 1
  | add p q hp hq => simp only [map_add, hp, hq]

end Tens

theorem tensIso_of_exact : ∀ (G LL O V : Type) [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) (L : Lattice (O := O) ρ) (χ : G →* Oˣ) (S X Y : Type) [AddCommGroup S] [Module O S] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (i : S →ₗ[O] X) (p : X →ₗ[O] Y), Function.Injective i → Function.Exact i p → Function.Surjective p → (∀ c x, tensCoc L χ X c x ∈ ReciprocityTheory.Def.Z1 (twCoef (latRep L) χ X) ⊤) → (∀ m, IsLocallyConstant fun g => twCoef (latRep L) χ X g m) → (twCoef (latRep L) χ Y).invariants = ⊥ → TensIso L χ S → TensIso L χ Y → TensIso L χ X := by
  intro G LL O V _ _ _ _ _ _ _ _ _ _ _ _ ρ L χ S X Y _ _ _ _ _ _ i p hi hex hp hcoc hlc hinv hS hY
  have := L.free
  refine five (i.lTensor ↥L.T) (p.lTensor ↥L.T) (lTensor_equivariant L χ i) (lTensor_equivariant L χ p)
    (Module.Flat.lTensor_preserves_injective_linearMap i hi) (lTensor_exact _ hex hp)
    (LinearMap.lTensor_surjective _ hp) (i.lTensor (H1tw L χ)) (p.lTensor (H1tw L χ))
    (lTensor_exact _ hex hp) (LinearMap.lTensor_surjective _ hp)
    (tensAmb L χ S) (tensAmb L χ X) (tensAmb L χ Y) (fun y => tensAmb_natural L χ i y)
    (fun y => tensAmb_natural L χ p y) ?_ hlc hinv hS hY
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul c x =>
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [tensAmb_tmul]
    exact (mem_range_toAmb _).2 ⟨_, hcoc c x, rfl⟩
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq

end GlobalTheory.TensIsoExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentCoeffNegEqZeroOfBounded
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

namespace GlobalTheory

theorem norm_eTwoPi_I_mul (y : ℝ) : ‖eTwoPi (Complex.I * y)‖ = Real.exp (-(2 * Real.pi * y)) := by
  rw [eTwoPi, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem laurent_coeff_neg_eq_zero_of_bounded : ∀ (F : ℂ⸨X⸩) (T C : ℝ),
    (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) →
    ∀ m : ℤ, m < 0 → F.coeff m = 0 := by
  intro F T C h m hm
  by_contra hne
  have hF : F ≠ 0 := by rintro rfl; exact hne (by simp)
  have hm₀le : F.order ≤ m := by
    by_contra hlt; push_neg at hlt; exact hne (HahnSeries.coeff_eq_zero_of_lt_order hlt)
  have hc : F.coeff F.order ≠ 0 := fun h0 => hF (HahnSeries.coeff_order_eq_zero.1 h0)
  obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat (le_of_lt (lt_of_le_of_lt hm₀le hm))
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
  set m₀ := F.order with hm₀
  set y₁ : ℝ := max T 0 + 1 with hy₁
  have hy₁T : T < y₁ := by have := le_max_left T 0; linarith
  have hy₁0 : 0 < y₁ := by have := le_max_right T 0; linarith
  obtain ⟨x₁, hx₁, -⟩ := h (Complex.I * y₁) (by simpa using hy₁T)
  set q₁ := eTwoPi (Complex.I * y₁) with hq₁
  set ρ₁ := ‖q₁‖ with hρ₁
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁, hq₁, norm_eTwoPi_I_mul]; exact Real.exp_pos _
  have hS : Summable (fun m : ℤ => ‖F.coeff m * q₁ ^ m‖) := hx₁.summable.norm
  set S := ∑' m : ℤ, ‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k with hSdef
  have key : ∀ y : ℝ, y₁ ≤ y →
      ‖F.coeff m₀‖ ≤ C * Real.exp (-(2 * Real.pi * y)) ^ k + Real.exp (-(2 * Real.pi * y)) / ρ₁ * S := by
    intro y hy
    obtain ⟨x, hx, hxC⟩ := h (Complex.I * y) (by simpa using lt_of_lt_of_le hy₁T hy)
    set q := eTwoPi (Complex.I * y) with hq
    set ρ := ‖q‖ with hρ
    have hρe : ρ = Real.exp (-(2 * Real.pi * y)) := norm_eTwoPi_I_mul y
    have hq0 : q ≠ 0 := Complex.exp_ne_zero _
    have hρle : ρ ≤ ρ₁ := by
      rw [hρe, hρ₁, hq₁, norm_eTwoPi_I_mul, Real.exp_le_exp]
      nlinarith [Real.pi_pos]
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    set r : ℤ → ℂ := fun m => F.coeff m * q ^ m * q ^ k - (if m = m₀ then F.coeff m₀ else 0) with hr
    have h2 : HasSum r (x * q ^ k - F.coeff m₀) := (hx.mul_right (q ^ k)).sub (hasSum_ite_eq m₀ _)
    have hbd : ∀ m, ‖r m‖ ≤ ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k) := by
      intro m
      have hRnn : 0 ≤ ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k) := by positivity
      by_cases hmm : m = m₀
      · subst hmm
        have : q ^ m₀ * q ^ k = 1 := by
          rw [hk, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hq0)]
        have : r m₀ = 0 := by simp only [hr, mul_assoc, this, mul_one]; simp
        rw [this, norm_zero]; exact hRnn
      rcases lt_or_gt_of_ne hmm with hlt | hgt
      · have : r m = 0 := by simp only [hr, if_neg hmm, HahnSeries.coeff_eq_zero_of_lt_order hlt, zero_mul, sub_zero]
        rw [this, norm_zero]; exact hRnn
      · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0:ℤ) ≤ m - m₀ - 1 by omega)
        have hm : m = (n + 1 : ℕ) - (k : ℤ) := by push_cast; omega
        have e1 : ∀ t : ℝ, t ≠ 0 → t ^ m * t ^ k = t ^ (n + 1) := fun t ht => by
          rw [← zpow_natCast t k, ← zpow_add₀ ht, ← zpow_natCast]; congr 1; omega
        have hρpos : 0 < ρ := by rw [hρe]; exact Real.exp_pos _
        have hrm : ‖r m‖ = ‖F.coeff m‖ * (ρ ^ m * ρ ^ k) := by
          simp only [hr, if_neg hmm, sub_zero, norm_mul, norm_pow, norm_zpow, ← hρ, mul_assoc]
        have hq₁m : ‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k = ‖F.coeff m‖ * (ρ₁ ^ m * ρ₁ ^ k) := by
          rw [norm_mul, norm_zpow, ← hρ₁, mul_assoc]
        rw [hrm, hq₁m, e1 ρ hρpos.ne', e1 ρ₁ hρ₁pos.ne']
        have hpow : ρ ^ n ≤ ρ₁ ^ n := pow_le_pow_left₀ hρ0 hρle n
        have hc0 : 0 ≤ ‖F.coeff m‖ := norm_nonneg _
        rw [pow_succ, pow_succ]
        calc ‖F.coeff m‖ * (ρ ^ n * ρ) ≤ ‖F.coeff m‖ * (ρ₁ ^ n * ρ) := by gcongr
          _ = ρ / ρ₁ * (‖F.coeff m‖ * (ρ₁ ^ n * ρ₁)) := by field_simp
    have hg : HasSum (fun m => ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k)) (ρ / ρ₁ * S) :=
      (hS.mul_right (ρ₁ ^ k)).hasSum.mul_left _
    have h3 : ‖x * q ^ k - F.coeff m₀‖ ≤ ρ / ρ₁ * S := by
      rw [← h2.tsum_eq]; exact tsum_of_norm_bounded hg hbd
    have h4 : ‖x * q ^ k‖ ≤ C * ρ ^ k := by
      rw [norm_mul, norm_pow]; exact mul_le_mul_of_nonneg_right hxC (by positivity)
    rw [← hρe]
    calc ‖F.coeff m₀‖ = ‖x * q ^ k - (x * q ^ k - F.coeff m₀)‖ := by ring_nf
      _ ≤ ‖x * q ^ k‖ + ‖x * q ^ k - F.coeff m₀‖ := norm_sub_le _ _
      _ ≤ C * ρ ^ k + ρ / ρ₁ * S := add_le_add h4 h3
  have hlim : Filter.Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
      (Filter.tendsto_id.const_mul_atTop (by positivity)))
  have hlim2 : Filter.Tendsto (fun y : ℝ => C * Real.exp (-(2 * Real.pi * y)) ^ k +
      Real.exp (-(2 * Real.pi * y)) / ρ₁ * S) Filter.atTop (nhds 0) := by
    have := ((hlim.pow k).const_mul C).add ((hlim.div_const ρ₁).mul_const S)
    simpa [zero_pow hk0] using this
  have hle : ‖F.coeff m₀‖ ≤ 0 :=
    ge_of_tendsto hlim2 (Filter.eventually_atTop.2 ⟨y₁, key⟩)
  exact hc (norm_le_zero_iff.1 hle)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftImageEulerEInvariantsQuotientStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_image_eulerE_invariants_quotient : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (F : BKHom D₀ D₁) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Image D₁ U → ∀ ω : D₁.Pol, (∃ w ∈ D₁.Zl, D₁.Lc w = ω) → ∀ c : ℕ, (∃ w₀ ∈ D₀.Zl, F.onPol w₀ = (l : K) ^ c • ω) → ∃ w ∈ D₀.Zl, F.onPol (D₀.Lc w) = ω := by
  first | exact @GlobalTheory.Proof.LiftImage.lift_image | exact GlobalTheory.Proof.LiftImage.lift_image | (intros; apply GlobalTheory.Proof.LiftImage.lift_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAnalyticFiltrationIffLatticeFiltrationAddStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_analytic_filtration_iff_lattice_filtration_add : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (i : ℤ) (x : Vec K a ι), x ∈ (P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) ⊔ shiftE l e 1 (P.ext (Rpi O K l e)) ↔ ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  first | exact @GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff | exact GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff | (intros; apply GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemEisensteinFiltrationEqEisensteinPowMulDiscStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_eisensteinFiltration_eq_eisenstein_pow_mul_disc : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), ∀ φ : S O K e, φ ∈ Fil O K l e j → ∃ q ∈ Rpi O K l e, (φ : K⟦X⟧) = E K l e ^ j * q := by
  first | exact @GlobalTheory.FilDiv.mem_Fil_eq_E_pow_mul | exact GlobalTheory.FilDiv.mem_Fil_eq_E_pow_mul | (intros; apply GlobalTheory.FilDiv.mem_Fil_eq_E_pow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPhiModuleLatticeOfAdicSeriesPrimePowTermsStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) → (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m) → w ∈ P.MM := by
  first | exact @GlobalTheory.BK.PhiMod.mem_MM_of_series | exact GlobalTheory.BK.PhiMod.mem_MM_of_series | (intros; apply GlobalTheory.BK.PhiMod.mem_MM_of_series <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDivisibilityOfDescentDatumStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_divisibility_of_descentDatum : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Divisible D := by
  first | exact @GlobalTheory.divisible_of_BKDat | exact GlobalTheory.divisible_of_BKDat | (intros; apply GlobalTheory.divisible_of_BKDat <;> assumption)
end

