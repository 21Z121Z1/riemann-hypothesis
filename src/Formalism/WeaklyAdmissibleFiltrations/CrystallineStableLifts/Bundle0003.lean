import Formalism.WeaklyAdmissibleFiltrations.DpcrisStable

-- bundled from Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.DPotCrisStableAndExistsPotentiallyCrystallineDat
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

section Top
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

def PeriodData.pcResTop (PD : PeriodData G Qp K₀ K B BdR) :
    PeriodData (⊤ : Subgroup G) Qp K₀ K B BdR where
  p := PD.p
  hp := PD.hp
  finK₀ := PD.finK₀
  finK := PD.finK
  σ := PD.σ
  σ_bij := PD.σ_bij
  actB := PD.actB.comp (⊤ : Subgroup G).subtype
  invB b hb := PD.invB b (fun g => hb ⟨g, Subgroup.mem_top g⟩)
  φ := PD.φ
  φ_inj := PD.φ_inj
  φ_K₀ := PD.φ_K₀
  φ_comm g b := PD.φ_comm g b
  actdR := PD.actdR.comp (⊤ : Subgroup G).subtype
  invdR b hb := PD.invdR b (fun g => hb ⟨g, Subgroup.mem_top g⟩)
  ι := PD.ι
  ι_inj := PD.ι_inj
  ι_comm g b := PD.ι_comm g b
  Fil := PD.Fil
  Fil_anti := PD.Fil_anti
  one_mem := PD.one_mem
  Fil_mul := PD.Fil_mul
  Fil_exh := PD.Fil_exh
  Fil_sep := PD.Fil_sep
  Fil_G g := PD.Fil_G g
  χ := PD.χ.comp (⊤ : Subgroup G).subtype
  t := PD.t
  t_unit := PD.t_unit
  t_act g := PD.t_act g
  t_φ := PD.t_φ
  mem_filtration_one := PD.mem_filtration_one
  not_mem_filtration_two := PD.not_mem_filtration_two
  fund := PD.fund

def PotCrysData.pcOfTop (PD : PeriodData G Qp K₀ K B BdR) : PotCrysData G Qp K₀ K K₀ K B BdR where
  H := ⊤
  normal := inferInstance
  finiteIndex := inferInstance
  PD := PD
  PD' := PD.pcResTop
  actB_eq _ _ := rfl
  actdR_eq _ _ := rfl
  φ_eq _ := rfl
  ι_eq _ := rfl
  Fil_eq _ := rfl
  p_eq := rfl
  t_eq := rfl
  χ_eq _ := rfl
  stableK₀' g c := ⟨c, AlgEquiv.commutes (PD.actB g) c⟩

end Top

section Stable
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem pc_actVB_mul (PD : PeriodData G Qp K₀ K B BdR) (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, map_mul, AlgebraTensorModule.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pc_actVB_res (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ (h : G) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, AlgebraTensorModule.map_tmul, PotCrysData.resH, PC.actB_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pc_mem_Dpcris {x : V ⊗[Qp] B} :
    x ∈ PC.Dpcris ρ ↔ ∀ h : PC.H, actVB PC.PD ρ (h : G) x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, pc_actVB_res]

theorem pc_Dpcris_stable (g : G) {x : V ⊗[Qp] B} (hx : x ∈ PC.Dpcris ρ) :
    actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  rw [pc_mem_Dpcris] at hx ⊢
  intro h
  have hmem : g⁻¹ * (h : G) * g ∈ PC.H := by
    have := PC.normal.conj_mem (h : G) h.2 g⁻¹
    rwa [inv_inv] at this
  have e : (h : G) * g = g * (g⁻¹ * (h : G) * g) := by group
  rw [← pc_actVB_mul, e, pc_actVB_mul, hx ⟨_, hmem⟩]

end Stable

theorem pc_dpcrisStable : DpcrisStable := by
  intros
  apply pc_Dpcris_stable
  all_goals assumption

theorem pc_exPC : ExPC := by
  unfold ExPC
  intros
  exact ⟨PotCrysData.pcOfTop _, rfl, rfl⟩

theorem dPotCrisStable_and_existsPotentiallyCrystallineData : DpcrisStable ∧ ExPC := ⟨pc_dpcrisStable, pc_exPC⟩

end Formalism.WeaklyAdmissibleFiltrations
end
end

-- bundled from Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.NegJumps
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

private theorem negJumps_Ico_telescope (f : ℤ → ℤ) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, (f a - f (a + 1)) = f m - f k := by
  induction k, hmk using Int.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [← Finset.Ico_union_Ico_eq_Ico hk (by omega),
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive m k (k + 1)), ih]
    have h1 : Finset.Ico k (k + 1) = {k} := by
      ext z
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [h1, Finset.sum_singleton]
    ring

theorem negativeJumpsSum_holds : NegJumps := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ τ lo _ hlo hF
  have h1 := negJumps_Ico_telescope (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) lo 0 hlo
  unfold multV
  rw [h1, hF]

end Formalism.WeaklyAdmissibleFiltrations
end
end

