import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0011
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CommonDenom
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.ProdEP2Uni

section LocTop

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem topE (M : Loc.Model F E) : IsTopologicalRing E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  first
    | exact IsModuleTopology.isTopologicalRing F E
    | exact IsModuleTopology.topologicalRing F E

theorem t2E (M : Loc.Model F E) : T2Space E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : T2Space F := MainNotions.LocalModelPeriodLattices.nonarchimedean_local_field_t2 inferInstance
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  let b := Module.Free.chooseBasis F E
  have hc : Continuous (b.equivFun : E → (Module.Free.ChooseBasisIndex F E → F)) :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  exact T2Space.of_injective_continuous b.equivFun.injective hc

theorem int_mem {x : F} (h : IsIntegral 𝒪[F] x) : x ∈ 𝒪[F] := by
  first
    | exact (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
    | (obtain ⟨y, hy⟩ := (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
       rw [← hy]
       exact y.2)

theorem alg_int (x : 𝒪[F]) : algebraMap F E (x : F) = algebraMap 𝒪[F] E x := by
  first
    | rfl
    | exact (IsScalarTower.algebraMap_apply 𝒪[F] F E x).symm

private theorem R_eq_O_of_split_eq_none (M : Loc.Model F E) (hg : M.split = none) : M.R = M.L.O := by
  simp only [Loc.Model.R, hg]

private theorem mem_R_iff_of_split_eq_some (M : Loc.Model F E) (g : Loc.SplitG M.L) (hg : M.split = some g) (z : E) :
    z ∈ M.R ↔ ∃ a b : 𝒪[F], g.e z = ((a : F), (b : F)) ∧
      Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b := by
  simp only [Loc.Model.R, hg, Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, b, he.symm, RingHom.mem_eqLocus.mp hab⟩
  · rintro ⟨a, b, he, hab⟩
    exact ⟨(a, b), RingHom.mem_eqLocus.mpr hab, he.symm⟩

theorem alg_mem_R (M : Loc.Model F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ M.R := by
  cases hg : M.split with
  | none =>
    rw [R_eq_O_of_split_eq_none M hg, M.L.O_def, alg_int]
    exact isIntegral_algebraMap
  | some g =>
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨a, a, ?_, rfl⟩
    rw [AlgEquiv.commutes]
    first
      | rfl
      | simp

private theorem splitG_e_mem_integers_of_mem_O (L : Loc.LocE F E) (g : Loc.SplitG L) {z : E} (hz : z ∈ L.O) :
    (g.e z).1 ∈ 𝒪[F] ∧ (g.e z).2 ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (g.e z) := ((L.O_def z).mp hz).map (g.e.toAlgHom.restrictScalars 𝒪[F])
  exact ⟨int_mem (h1.map ((AlgHom.fst F F F).restrictScalars 𝒪[F])),
    int_mem (h1.map ((AlgHom.snd F F F).restrictScalars 𝒪[F]))⟩

private theorem mem_O_of_mem_R (M : Loc.Model F E) {z : E} (hz : z ∈ M.R) : z ∈ M.L.O := by
  cases hg : M.split with
  | none =>
    rwa [R_eq_O_of_split_eq_none M hg] at hz
  | some g =>
    obtain ⟨a, b, he, -⟩ := (mem_R_iff_of_split_eq_some M g hg z).mp hz
    rw [M.L.O_def]
    have ha : IsIntegral 𝒪[F] (a : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F a))
    have hb : IsIntegral 𝒪[F] (b : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F b))
    have h1 : IsIntegral 𝒪[F] (((a : F), (b : F)) : F × F) := IsIntegral.pair ha hb
    have h2 := h1.map (g.e.symm.toAlgHom.restrictScalars 𝒪[F])
    rw [← he] at h2
    have e : (g.e.symm.toAlgHom.restrictScalars 𝒪[F]) (g.e z) = z := g.e.symm_apply_apply z
    rwa [e] at h2

theorem R_compact [CharZero F] (M : Loc.Model F E) : IsCompact (M.R : Set E) := by
  haveI := topE M
  have hO := (MainNotions.LocalModelPeriodLattices.O_top M.L).2.1
  have hRo : IsOpen (M.R : Set E) := PI.ProdFormulaE.ROpen.isOpen_R M
  have hRc : IsClosed (M.R : Set E) := M.R.toAddSubgroup.isClosed_of_isOpen hRo
  exact hO.of_isClosed_subset hRc (fun z hz => mem_O_of_mem_R M hz)

theorem R_denom (M : Loc.Model F E) (y : E) : ∃ a : 𝒪[F], a ≠ 0 ∧ algebraMap F E (a : F) * y ∈ M.R := by
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  haveI : Nontrivial E := by
    first
      | exact Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
      | exact Module.nontrivial_of_finrank_eq_succ M.L.rank
  haveI : IsFractionRing 𝒪[F] F := ValuationRing.instIsFractionRingInteger (ValuativeRel.valuation F)
  have hinj : ∀ x : 𝒪[F], algebraMap 𝒪[F] E x = 0 → x = 0 := by
    intro x hx
    rw [← alg_int] at hx
    exact Subtype.ext ((map_eq_zero_iff _ (algebraMap F E).injective).mp hx)
  have halg : IsAlgebraic 𝒪[F] y := by
    have hF : IsAlgebraic F y := (Algebra.IsIntegral.isIntegral (R := F) y).isAlgebraic
    exact (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).mpr hF
  have hex : ∃ s : 𝒪[F], s ≠ 0 ∧ IsIntegral 𝒪[F] (algebraMap 𝒪[F] E s * y) := by
    first
      | (obtain ⟨z, s, hs, hz⟩ := exists_integral_multiple halg hinj
         exact ⟨s, hs, by rw [mul_comm, hz]; exact z.2⟩)
      | (obtain ⟨s, hs, hi⟩ := halg.exists_integral_multiple
         exact ⟨s, hs, by rwa [Algebra.smul_def] at hi⟩)
  obtain ⟨s, hs, hsi⟩ := hex
  have hsy : algebraMap F E (s : F) * y ∈ M.L.O := by
    rw [M.L.O_def, alg_int]
    exact hsi
  cases hg : M.split with
  | none =>
    exact ⟨s, hs, by rw [R_eq_O_of_split_eq_none M hg]; exact hsy⟩
  | some g =>
    refine ⟨g.q * s, mul_ne_zero g.q_irr.ne_zero hs, ?_⟩
    obtain ⟨h1, h2⟩ := splitG_e_mem_integers_of_mem_O M.L g hsy
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨g.q * ⟨_, h1⟩, g.q * ⟨_, h2⟩, ?_, ?_⟩
    · have e : algebraMap F E ((g.q * s : 𝒪[F]) : F) * y =
          algebraMap F E (g.q : F) * (algebraMap F E (s : F) * y) := by
        rw [MulMemClass.coe_mul, map_mul, mul_assoc]
      rw [e, map_mul, AlgEquiv.commutes]
      ext <;> simp
    · have hq : ∀ t : 𝒪[F], Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * t) = 0 := fun t =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right t _ (Ideal.mem_span_singleton_self _))
      rw [hq, hq]

theorem common_denom (M : Loc.Model F E) {ι : Type} [Fintype ι] (y : ι → E) :
    ∃ a : 𝒪[F], a ≠ 0 ∧ ∀ k, algebraMap F E (a : F) * y k ∈ M.R := by
  classical
  choose d hd0 hd using fun k => R_denom M (y k)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩
  have hp : (∏ j, d j) = (∏ j ∈ Finset.univ.erase k, d j) * d k :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ k)).symm
  rw [hp]
  have e : algebraMap F E (((∏ j ∈ Finset.univ.erase k, d j) * d k : 𝒪[F]) : F) * y k =
      algebraMap F E ((∏ j ∈ Finset.univ.erase k, d j : 𝒪[F]) : F) * (algebraMap F E (d k : F) * y k) := by
    rw [MulMemClass.coe_mul, map_mul, mul_assoc]
  rw [e]
  exact M.R.mul_mem (alg_mem_R M _) (hd k)

end LocTop

end Formalism.L2.SG.Pf.ProdEP2Uni
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DensCongPf
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel

section Act

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι]

def act (A : Matrix ι ι E) (v : ι → V) : ι → V := fun b => ∑ a, A a b • v a

theorem act_act (A B : Matrix ι ι E) (v : ι → V) : act A (act B v) = act (B * A) v := by
  funext b
  simp only [act, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem h_sum_left {κ : Type} (s : Finset κ) (f : κ → V) (y : V) : H.h (∑ c ∈ s, f c) y = ∑ c ∈ s, H.h (f c) y := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact H.h_zero_left y
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, H.h_add_left, ih]

theorem h_right (x y : V) : H.h x y = M.L.cj (H.h y x) := by
  rw [H.h_herm x y, M.L.cj_cj]

theorem h_sum_right {κ : Type} (s : Finset κ) (f : κ → V) (x : V) : H.h x (∑ c ∈ s, f c) = ∑ c ∈ s, H.h x (f c) := by
  rw [h_right, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun c _ => (h_right H x (f c)).symm

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [h_right, H.h_smul_left, map_mul, ← h_right]

theorem gram_act (A : Matrix ι ι E) (v : ι → V) (a b : ι) :
    H.h (act A v b) (act A v a) =
      ((A.map M.L.cj).transpose * Matrix.of (fun c d => H.h (v d) (v c)) * A) a b := by
  simp only [act, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  rw [h_sum_left]
  simp only [H.h_smul_left, h_sum_right, h_smul_right, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

end Act

end Formalism.L2.SG.Pf.DensCongPf

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel
open scoped Matrix

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem act_one (v : ι → V) : act (1 : Matrix ι ι E) v = v := by
  funext b
  simp only [act, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem o_mul_mem (S : Submodule M.L.O E) {o x : E} (ho : o ∈ M.L.O) (hx : x ∈ S) : o * x ∈ S :=
  S.smul_mem ⟨o, ho⟩ hx

theorem cong_act (S : Submodule M.L.O E) (A G : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V)
    (hv : ∀ a b, H.h (v b) (v a) - G a b ∈ S) :
    ∀ a b, H.h (act A v b) (act A v a) - ((A.map M.L.cj).transpose * G * A) a b ∈ S := by
  intro a b
  rw [gram_act, ← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.of_apply]
  refine S.sum_mem fun c _ => ?_
  rw [Finset.sum_mul]
  refine S.sum_mem fun d _ => ?_
  rw [mul_comm _ (A c b), ← mul_assoc]
  rw [mul_comm (A c b)]
  refine o_mul_mem S (Subring.mul_mem _ (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (hAO d a)) (hAO c b)) (hv d c)

theorem mem_lam_act (abelian₂ : Submodule M.L.O V) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V)
    (hv : ∀ a, v a ∈ abelian₂) (b : ι) : act A v b ∈ abelian₂ :=
  abelian₂.sum_mem fun a _ => abelian₂.smul_mem ⟨A a b, hAO a b⟩ (hv a)

theorem mem_span_act (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V) (b : ι) :
    act A v b ∈ Submodule.span M.L.O (Set.range v) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (⟨A a b, hAO a b⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)

theorem mem_spanE_act (A : Matrix ι ι E) (v : ι → V) (b : ι) :
    act A v b ∈ Submodule.span E (Set.range v) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (A a b) (Submodule.subset_span ⟨a, rfl⟩)

theorem prim_act (abelian₂ : Submodule M.L.O V) (A B : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (hBO : ∀ i j, B i j ∈ M.L.O) (hAB : A * B = 1) (hBA : B * A = 1) (v : ι → V) (hv : H.Prim abelian₂ v) :
    H.Prim abelian₂ (act A v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  have hback : act B (act A v) = v := by rw [act_act, hAB, act_one]
  refine ⟨mem_lam_act abelian₂ A hAO v h1, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff] at h2 ⊢
    intro g hg
    have e : ∑ b, g b • act A v b = ∑ a, (A *ᵥ g) a • v a := by
      simp only [act, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
    rw [e] at hg
    have h0 := h2 _ hg
    have hAg : A *ᵥ g = 0 := funext h0
    have : g = B *ᵥ (A *ᵥ g) := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    intro b
    rw [this, hAg, Matrix.mulVec_zero]
    rfl
  · intro x hx hxs
    have hxv : x ∈ Submodule.span E (Set.range v) := by
      refine Submodule.span_le.2 ?_ hxs
      rintro _ ⟨b, rfl⟩
      exact mem_spanE_act A v b
    have hO := h3 x hx hxv
    refine Submodule.span_le.2 ?_ hO
    rintro _ ⟨a, rfl⟩
    have : v a = act B (act A v) a := by rw [hback]
    rw [SetLike.mem_coe, this]
    exact mem_span_act B hBO (act A v) a

end Main

end Formalism.L2.SG.Pf.DensCongPf

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel
open scoped Matrix

section Count

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem det_mem (A : Matrix ι ι E) (hA : ∀ i j, A i j ∈ M.L.O) : A.det ∈ M.L.O := by
  rw [Matrix.det_apply]
  exact M.L.O.sum_mem fun σ _ => Subring.zsmul_mem _ (M.L.O.prod_mem fun i _ => hA _ _) _

theorem adj_mem (A : Matrix ι ι E) (hA : ∀ i j, A i j ∈ M.L.O) : ∀ i j, A.adjugate i j ∈ M.L.O := by
  intro i j
  rw [Matrix.adjugate_apply]
  refine det_mem _ fun a b => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs; exacts [M.L.O.one_mem, M.L.O.zero_mem]
  · exact hA a b

def cls (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) (G₀ : Matrix ι ι E) :
    Set (ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) abelian₂) :=
  Set.range fun v : {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
    fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) abelian₂) (v.1 a)

def psi (abelian₂ : Submodule M.L.O V) (c : E) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (x : ι → V ⧸ H.smulLat c abelian₂) : ι → V ⧸ H.smulLat c abelian₂ :=
  fun b => ∑ a, (⟨A a b, hAO a b⟩ : M.L.O) • x a

theorem psi_mk (abelian₂ : Submodule M.L.O V) (c : E) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V) :
    psi H abelian₂ c A hAO (fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (v a)) =
      fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (act A v a) := by
  funext b
  simp only [psi, act]
  rw [show (Submodule.Quotient.mk (∑ a, A a b • v a) : V ⧸ H.smulLat c abelian₂) =
    (H.smulLat c abelian₂).mkQ (∑ a, A a b • v a) from rfl, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show _ = (H.smulLat c abelian₂).mkQ ((⟨A a b, hAO a b⟩ : M.L.O) • v a)
  rw [LinearMap.map_smul]
  rfl

theorem psi_psi (abelian₂ : Submodule M.L.O V) (c : E) (A B : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (hBO : ∀ i j, B i j ∈ M.L.O) (hAB : A * B = 1) (x : ι → V ⧸ H.smulLat c abelian₂) :
    psi H abelian₂ c B hBO (psi H abelian₂ c A hAO x) = x := by
  funext b
  simp only [psi, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ a, ∑ y, ((⟨B y b, hBO y b⟩ : M.L.O) * ⟨A a y, hAO a y⟩) • x a =
      (if a = b then (1 : M.L.O) else 0) • x a := by
    intro a
    rw [← Finset.sum_smul]
    congr 1
    apply Subtype.ext
    have h := congrFun (congrFun hAB a) b
    rw [Matrix.mul_apply] at h
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
    rw [Finset.sum_congr rfl (fun y _ => mul_comm (B y b) (A a y)), h, Matrix.one_apply]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp

theorem densCong_body (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) (G A : Matrix ι ι E)
    (hAO : ∀ i j, A i j ∈ M.L.O) (hAd : ∃ y ∈ M.L.O, A.det * y = 1) :
    H.dens ϖ abelian₂ ((A.map M.L.cj).transpose * G * A) = H.dens ϖ abelian₂ G := by
  obtain ⟨y, hy, hdy⟩ := hAd
  set B : Matrix ι ι E := y • A.adjugate with hB
  have hBO : ∀ i j, B i j ∈ M.L.O := fun i j => by
    rw [hB, Matrix.smul_apply, smul_eq_mul]; exact Subring.mul_mem _ hy (adj_mem A hAO i j)
  have hAB : A * B = 1 := by
    rw [hB, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm, hdy, one_smul]
  have hBA : B * A = 1 := by
    rw [hB, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm, hdy, one_smul]
  set c : E := algebraMap F E (ϖ : F)
  set S : Submodule M.L.O E := Submodule.span M.L.O {c}
  set G' := (A.map M.L.cj).transpose * G * A with hG'
  have hGback : (B.map M.L.cj).transpose * G' * B = G := by
    have e1 : (B.map M.L.cj).transpose * (A.map M.L.cj).transpose = 1 := by
      rw [← Matrix.transpose_mul]
      have : A.map M.L.cj * B.map M.L.cj = (A * B).map M.L.cj := by
        ext i j; simp [Matrix.mul_apply, map_sum]
      rw [this, hAB]
      ext i j; simp [Matrix.one_apply, eq_comm]
    rw [hG', ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, hAB, Matrix.mul_one]
  have hset : cls H ϖ abelian₂ G' = psi H abelian₂ c A hAO '' cls H ϖ abelian₂ G := by
    ext x
    constructor
    · rintro ⟨⟨v', hP, hC⟩, rfl⟩
      refine ⟨fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (act B v' a),
        ⟨⟨act B v', prim_act H abelian₂ B A hBO hAO hBA hAB v' hP, ?_⟩, rfl⟩, ?_⟩
      · have := cong_act H S B G' hBO v' hC
        rwa [hGback] at this
      · show psi H abelian₂ c A hAO (fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (act B v' a)) = _
        rw [psi_mk, act_act, hBA, act_one]
    · rintro ⟨_, ⟨⟨v, hP, hC⟩, rfl⟩, rfl⟩
      refine ⟨⟨act A v, prim_act H abelian₂ A B hAO hBO hAB hBA v hP, cong_act H S A G hAO v hC⟩, ?_⟩
      exact (psi_mk H abelian₂ c A hAO v).symm
  have hinj : Function.Injective (psi H abelian₂ c A hAO) := fun x x' h => by
    rw [← psi_psi H abelian₂ c A B hAO hBO hAB x, ← psi_psi H abelian₂ c A B hAO hBO hAB x', h]
  have hcard : Nat.card (cls H ϖ abelian₂ G') = Nat.card (cls H ϖ abelian₂ G) := by
    rw [hset, Nat.card_image_of_injective hinj]
  unfold Loc.HermSp.dens
  exact congrArg (fun n : ℕ => (n : ℝ) / _) hcard

end Count

end Formalism.L2.SG.Pf.DensCongPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLocJacHypLemmas
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.SG.LocVol.LJP

theorem hE_crdOf {D : D7} (X : HidaSetting D) (x y : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.HidaSetting.crdOf X.B.I X.ιE X.bas x) (Formalism.L2.SG.HidaSetting.crdOf X.B.I X.ιE X.bas y) =
      X.ιE.symm ((VS D).hT x y) := by
  apply X.ιE.injective
  rw [RingEquiv.apply_symm_apply, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y]
  rfl

theorem diag : DiagProp := by
  intro D X w v
  have hze : ∀ a, (VS D).hT (X.zu w) (X.eX a) = 0 := by
    intro a
    have h := (VS D).herm.eq (X.eX a) (X.zu w)
    rw [(X.zu_orth w a).1] at h
    simpa using h.symm
  ext a b
  simp only [TFv, Matrix.map_apply, Matrix.diagonal_apply, gramE]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, hE_crdOf, X.zu_norm, Tw]
    | cast j => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, Fin.snoc_castSucc, hE_crdOf, hze, Ne.symm (Fin.castSucc_ne_last j)]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, Fin.snoc_castSucc, hE_crdOf, (X.zu_orth w i).1, Fin.castSucc_ne_last]
    | cast j => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_castSucc, hE_crdOf, X.ee, Fin.castSucc_ne_last]

theorem herm : HermProp := by
  intro D X w v
  rw [diag X w v]
  intro a b
  by_cases h : a = b
  · subst h
    simp only [Matrix.diagonal_apply_eq]
    split_ifs <;> simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem integral : IntProp := by
  intro D X u u' v _ hdiv i j
  rw [diag X u' v, diag X u v]
  by_cases h : i = j ∧ i = Fin.last D.R.rS
  · obtain ⟨rfl, rfl⟩ := h
    obtain ⟨k, hk⟩ := hdiv
    simp only [Matrix.diagonal_apply_eq, if_true]
    letI : CharZero (Fv X.B.I.F v) := charZero_of_injective_algebraMap (algebraMap X.B.I.F (Fv X.B.I.F v)).injective
    have hg : ((gAt X v : ℕ) : Fv X.B.I.F v) ≠ 0 := Nat.cast_ne_zero.2 (gAt_prime X v).ne_zero
    have hA : ((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - ((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) =
        ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * (k : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := by
      have := congrArg (Int.cast : ℤ → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) hk
      push_cast at this
      exact this
    have hs : ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) *
        sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = 1 := by
      rw [show sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ =
          Algebra.TensorProduct.includeLeftRingHom (R := X.B.I.F) (B := X.B.I.E) ((gAt X v : Fv X.B.I.F v))⁻¹ from rfl,
        ← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := X.B.I.F) (A := Fv X.B.I.F v) (B := X.B.I.E)),
        ← map_mul, mul_inv_cancel₀ hg, map_one]
    have e1 : (-((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - -((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) *
        sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = inclR (Fv X.B.I.F v) ((k : 𝓞 X.B.I.E) : X.B.I.E) := by
      rw [show -((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - -((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) =
          ((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - ((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) by ring,
        hA, mul_comm ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E), mul_assoc, hs, mul_one]
      simp
    rw [e1]
    unfold OEv
    exact Submodule.subset_span ⟨(k : 𝓞 X.B.I.E), Set.mem_univ _, rfl⟩
  · have h0 : ∀ d : Fin (D.R.rS + 1) → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, (∀ l, l ≠ Fin.last D.R.rS → d l = 0) →
        Matrix.diagonal d i j = 0 := by
      intro d hd
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq]; exact hd _ (fun h' => h ⟨rfl, h'⟩)
      · exact Matrix.diagonal_apply_ne _ hij
    rw [h0 _ (fun l hl => if_neg hl), h0 _ (fun l hl => if_neg hl), sub_zero, zero_mul]
    unfold OEv
    exact Submodule.zero_mem _

end Formalism.L2.SG.LocVol.LJP
end

