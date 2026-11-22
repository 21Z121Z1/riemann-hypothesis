import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMovedHomLatticeEqProdHalvesSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section

namespace GlobalTheory.SplitIdxDec

open GlobalTheory.PlaceModel GlobalTheory.FinWeilO

variable {D : D7} {S T : HSp D}

theorem smul_mem_half {e : AE D} (he : e * e = e) (x : WO S T) : e • x ∈ half S T e := by
  rw [mem_half, smul_smul, he]

theorem smul_eq_zero_of_mem_half {e f : AE D} (hef : e * f = 0) {x : WO S T} (hx : x ∈ half S T f) :
    e • x = 0 := by
  rw [← (mem_half S T).1 hx, smul_smul, hef, zero_smul]

theorem smul_add_add_WO (e : AE D) (x y z : WO S T) : e • (x + y + z) = e • x + e • y + e • z := by
  rw [smul_add, smul_add]

def proj3 (B : AddSubgroup (WO S T)) {e₁ e₂ e₃ : AE D} (h1 : e₁ * e₁ = e₁) (h2 : e₂ * e₂ = e₂)
    (h3 : e₃ * e₃ = e₃) (hB : ∀ b ∈ B, e₁ • b ∈ B ∧ e₂ • b ∈ B ∧ e₃ • b ∈ B) :
    B →+ (B ⊓ half S T e₁ : AddSubgroup (WO S T)) × (B ⊓ half S T e₂ : AddSubgroup (WO S T)) ×
      (B ⊓ half S T e₃ : AddSubgroup (WO S T)) where
  toFun b := (⟨e₁ • (b : WO S T), (hB b b.2).1, smul_mem_half h1 _⟩,
    ⟨e₂ • (b : WO S T), (hB b b.2).2.1, smul_mem_half h2 _⟩,
    ⟨e₃ • (b : WO S T), (hB b b.2).2.2, smul_mem_half h3 _⟩)
  map_zero' := Prod.ext (Subtype.ext (smul_zero _)) (Prod.ext (Subtype.ext (smul_zero _)) (Subtype.ext (smul_zero _)))
  map_add' x y := Prod.ext (Subtype.ext (smul_add _ _ _))
    (Prod.ext (Subtype.ext (smul_add _ _ _)) (Subtype.ext (smul_add _ _ _)))

theorem part_eq {e f g : AE D} {x y z : WO S T} (hx : x ∈ half S T e) (hy : y ∈ half S T f) (hz : z ∈ half S T g)
    (hef : e * f = 0) (heg : e * g = 0) : e • (x + y + z) = x := by
  rw [smul_add_add_WO, (mem_half S T).1 hx, smul_eq_zero_of_mem_half hef hy, smul_eq_zero_of_mem_half heg hz,
    add_zero, add_zero]

theorem projThreeIdempotentHalves_surjective (B : AddSubgroup (WO S T)) {e₁ e₂ e₃ : AE D} (h1 : e₁ * e₁ = e₁) (h2 : e₂ * e₂ = e₂)
    (h3 : e₃ * e₃ = e₃) (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0)
    (hB : ∀ b ∈ B, e₁ • b ∈ B ∧ e₂ • b ∈ B ∧ e₃ • b ∈ B) :
    Function.Surjective (proj3 B h1 h2 h3 hB) := by
  rintro ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩, ⟨b₃, hb₃⟩⟩
  have h21 : e₂ * e₁ = 0 := by rw [mul_comm, h12]
  have h31 : e₃ * e₁ = 0 := by rw [mul_comm, h13]
  have h32 : e₃ * e₂ = 0 := by rw [mul_comm, h23]
  have c2 : e₂ • (b₂ + b₁ + b₃) = b₂ := part_eq hb₂.2 hb₁.2 hb₃.2 h21 h23
  have c3 : e₃ • (b₃ + b₁ + b₂) = b₃ := part_eq hb₃.2 hb₁.2 hb₂.2 h31 h32
  rw [show b₂ + b₁ + b₃ = b₁ + b₂ + b₃ by abel] at c2
  rw [show b₃ + b₁ + b₂ = b₁ + b₂ + b₃ by abel] at c3
  exact ⟨⟨b₁ + b₂ + b₃, add_mem (add_mem hb₁.1 hb₂.1) hb₃.1⟩, Prod.ext (Subtype.ext (part_eq hb₁.2 hb₂.2 hb₃.2 h12 h13))
    (Prod.ext (Subtype.ext c2) (Subtype.ext c3))⟩

theorem projThreeIdempotentHalves_apply (B : AddSubgroup (WO S T)) {e₁ e₂ e₃ : AE D} (h1 : e₁ * e₁ = e₁) (h2 : e₂ * e₂ = e₂)
    (h3 : e₃ * e₃ = e₃) (hB : ∀ b ∈ B, e₁ • b ∈ B ∧ e₂ • b ∈ B ∧ e₃ • b ∈ B) (b : B) :
    ((proj3 B h1 h2 h3 hB b).1 : WO S T) = e₁ • (b : WO S T) ∧
      ((proj3 B h1 h2 h3 hB b).2.1 : WO S T) = e₂ • (b : WO S T) ∧
      ((proj3 B h1 h2 h3 hB b).2.2 : WO S T) = e₃ • (b : WO S T) := ⟨rfl, rfl, rfl⟩

theorem relIndex_three {A B : AddSubgroup (WO S T)} {e₁ e₂ e₃ : AE D}
    (h1 : e₁ * e₁ = e₁) (h2 : e₂ * e₂ = e₂) (h3 : e₃ * e₃ = e₃)
    (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0) (hs : e₁ + e₂ + e₃ = 1)
    (hA : ∀ a ∈ A, e₁ • a ∈ A ∧ e₂ • a ∈ A ∧ e₃ • a ∈ A)
    (hB : ∀ b ∈ B, e₁ • b ∈ B ∧ e₂ • b ∈ B ∧ e₃ • b ∈ B) :
    A.relIndex B = (A ⊓ half S T e₁).relIndex (B ⊓ half S T e₁) *
      ((A ⊓ half S T e₂).relIndex (B ⊓ half S T e₂) * (A ⊓ half S T e₃).relIndex (B ⊓ half S T e₃)) := by
  have hcomap : A.addSubgroupOf B = (((A ⊓ half S T e₁).addSubgroupOf (B ⊓ half S T e₁)).prod
      (((A ⊓ half S T e₂).addSubgroupOf (B ⊓ half S T e₂)).prod
        ((A ⊓ half S T e₃).addSubgroupOf (B ⊓ half S T e₃)))).comap (proj3 B h1 h2 h3 hB) := by
    refine AddSubgroup.ext fun b => ?_
    obtain ⟨k₁, k₂, k₃⟩ := projThreeIdempotentHalves_apply B h1 h2 h3 hB b
    constructor
    · intro hb
      have hb' : (b : WO S T) ∈ A := AddSubgroup.mem_addSubgroupOf.1 hb
      refine AddSubgroup.mem_comap.2 (AddSubgroup.mem_prod.2 ⟨?_, AddSubgroup.mem_prod.2 ⟨?_, ?_⟩⟩)
      · refine AddSubgroup.mem_addSubgroupOf.2 (AddSubgroup.mem_inf.2 ⟨?_, ?_⟩)
        · rw [k₁]; exact (hA _ hb').1
        · rw [k₁]; exact smul_mem_half h1 _
      · refine AddSubgroup.mem_addSubgroupOf.2 (AddSubgroup.mem_inf.2 ⟨?_, ?_⟩)
        · rw [k₂]; exact (hA _ hb').2.1
        · rw [k₂]; exact smul_mem_half h2 _
      · refine AddSubgroup.mem_addSubgroupOf.2 (AddSubgroup.mem_inf.2 ⟨?_, ?_⟩)
        · rw [k₃]; exact (hA _ hb').2.2
        · rw [k₃]; exact smul_mem_half h3 _
    · intro hb
      obtain ⟨p₁, p₂⟩ := AddSubgroup.mem_prod.1 (AddSubgroup.mem_comap.1 hb)
      obtain ⟨p₂, p₃⟩ := AddSubgroup.mem_prod.1 p₂
      have a₁ := (AddSubgroup.mem_inf.1 (AddSubgroup.mem_addSubgroupOf.1 p₁)).1
      have a₂ := (AddSubgroup.mem_inf.1 (AddSubgroup.mem_addSubgroupOf.1 p₂)).1
      have a₃ := (AddSubgroup.mem_inf.1 (AddSubgroup.mem_addSubgroupOf.1 p₃)).1
      rw [k₁] at a₁
      rw [k₂] at a₂
      rw [k₃] at a₃
      refine AddSubgroup.mem_addSubgroupOf.2 ?_
      have e : (b : WO S T) = e₁ • (b : WO S T) + e₂ • (b : WO S T) + e₃ • (b : WO S T) := by
        rw [← add_smul, ← add_smul, hs, one_smul]
      rw [e]
      exact add_mem (add_mem a₁ a₂) a₃
  rw [AddSubgroup.relIndex, hcomap,
    AddSubgroup.index_comap_of_surjective _ (projThreeIdempotentHalves_surjective B h1 h2 h3 h12 h13 h23 hB), AddSubgroup.index_prod,
    AddSubgroup.index_prod]
  rfl

theorem map_inf_half {Λ : AddSubgroup (WO S T)} {φ : WO S T →+ WO S T} {e : AE D} (he : e * e = e)
    (hΛ : ∀ a ∈ Λ, e • a ∈ Λ) (hφ : ∀ x, φ (e • x) = e • φ x) :
    Λ.map φ ⊓ half S T e = (Λ ⊓ half S T e).map φ := by
  refine AddSubgroup.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨⟨x, hx, rfl⟩, h2⟩ := AddSubgroup.mem_inf.1 hy
    refine ⟨e • x, AddSubgroup.mem_inf.2 ⟨hΛ x hx, smul_mem_half he x⟩, ?_⟩
    rw [hφ]
    exact (mem_half S T).1 h2
  · obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.1 hx
    refine AddSubgroup.mem_inf.2 ⟨⟨x, hx1, rfl⟩, ?_⟩
    rw [mem_half, ← hφ, (mem_half S T).1 hx2]

theorem actL_apply (g : GA D T) (x : WO S T) : GlobalTheory.SplitIdx.actL S T g x = actO S T 1 g x := rfl

theorem actL_smul (g : GA D T) (a : AE D) (x : WO S T) :
    GlobalTheory.SplitIdx.actL S T g (a • x) = a • GlobalTheory.SplitIdx.actL S T g x := by
  rw [actL_apply, actL_apply, actO_smul]

theorem actL_of_killed {g : GA D T} {r : AE D}
    (hr : r • (Formalism.L2.Theta.mt T g - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) = 0) {x : WO S T}
    (hx : x ∈ half S T r) : GlobalTheory.SplitIdx.actL S T g x = x := by
  rw [actL_apply, actO, inv_one, mt_one, Matrix.mul_one]
  have h : @HMul.hMul (Matrix (Fin T.rank) (Fin T.rank) (AE D)) (Matrix (Fin T.rank) (Fin S.rank) (AE D))
      (Matrix (Fin T.rank) (Fin S.rank) (AE D)) _ (Formalism.L2.Theta.mt T g - 1) x = 0 := by
    rw [← (mem_half S T).1 hx, Matrix.mul_smul, ← Matrix.smul_mul, hr, Matrix.zero_mul]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h

theorem rest_idem {R : Type} [CommRing R] {e f r : R} (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hr : r = 1 - e - f) :
    r * r = r ∧ e * r = 0 ∧ f * r = 0 ∧ e + f + r = 1 ∧ r * (e + f) = 0 := by
  subst hr
  refine ⟨by linear_combination he + hf + 2 * hef, by linear_combination -he - hef,
    by linear_combination -hf - hef, by ring, by linear_combination -he - hf - 2 * hef⟩

theorem kill_of_supp {g : GA D T} {r ε : AE D} (hr0 : r * (ε + cA D ε) = 0)
    (hg' : ∀ i j, (ε + cA D ε) * (Formalism.L2.Theta.mt T g - 1) i j = (Formalism.L2.Theta.mt T g - 1) i j) :
    r • (Formalism.L2.Theta.mt T g - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, ← hg' i j, ← mul_assoc, hr0, zero_mul]

theorem split_index {Λ : AddSubgroup (WO S T)} {g : GA D T} {ε c r : AE D}
    (he : ε * ε = ε) (h2 : c * c = c) (h3 : r * r = r) (hec : ε * c = 0) (h13 : ε * r = 0) (h23 : c * r = 0)
    (hsum : ε + c + r = 1) (hkill : r • (Formalism.L2.Theta.mt T g - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) = 0)
    (stε : ∀ a ∈ Λ, ε • a ∈ Λ) (stc : ∀ a ∈ Λ, c • a ∈ Λ) (str : ∀ a ∈ Λ, r • a ∈ Λ) :
    Λ.relIndex (Λ.map (GlobalTheory.SplitIdx.actL S T g)) =
      (Λ ⊓ half S T ε).relIndex ((Λ ⊓ half S T ε).map (GlobalTheory.SplitIdx.actL S T g)) *
      (Λ ⊓ half S T c).relIndex ((Λ ⊓ half S T c).map (GlobalTheory.SplitIdx.actL S T g)) := by
  have stφ : ∀ (e : AE D), (∀ a ∈ Λ, e • a ∈ Λ) → ∀ b ∈ Λ.map (GlobalTheory.SplitIdx.actL S T g),
      e • b ∈ Λ.map (GlobalTheory.SplitIdx.actL S T g) := by
    rintro e hst _ ⟨a, ha, rfl⟩
    exact ⟨e • a, hst a ha, actL_smul g e a⟩
  have key := relIndex_three he h2 h3 hec h13 h23 hsum (fun a ha => ⟨stε a ha, stc a ha, str a ha⟩)
    (fun b hb => ⟨stφ ε stε b hb, stφ c stc b hb, stφ r str b hb⟩)
  rw [map_inf_half he stε (actL_smul g ε), map_inf_half h2 stc (actL_smul g c),
    map_inf_half h3 str (actL_smul g r)] at key
  have hid : (Λ ⊓ half S T r).map (GlobalTheory.SplitIdx.actL S T g) = Λ ⊓ half S T r := by
    refine AddSubgroup.ext fun y => ⟨?_, fun hy => ⟨y, hy, actL_of_killed hkill (AddSubgroup.mem_inf.1 hy).2⟩⟩
    rintro ⟨x, hx, rfl⟩
    rwa [actL_of_killed hkill (AddSubgroup.mem_inf.1 hx).2]
  rw [hid, AddSubgroup.relIndex_self, mul_one] at key
  exact key

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts in

theorem idx_dec : ∀ (D : D7) (S T : HSp D) (ε : AE D), IsSplitIdem D ε → ∀ g : GA D T, SuppAt ε T g →
    GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T))
      ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, g))) =
    (GlobalTheory.SplitIdx.halfLat S T ε).relIndex ((GlobalTheory.SplitIdx.halfLat S T ε).map (GlobalTheory.SplitIdx.actL S T g)) *
    (GlobalTheory.SplitIdx.halfLat S T (cA D ε)).relIndex ((GlobalTheory.SplitIdx.halfLat S T (cA D ε)).map (GlobalTheory.SplitIdx.actL S T g)) := by
  intro D S T ε hε g hg
  have hg' : ∀ i j, (ε + cA D ε) * (Formalism.L2.Theta.mt T g - 1) i j = (Formalism.L2.Theta.mt T g - 1) i j := hg
  obtain ⟨he, hec, v, ε', hv, heq⟩ := hε
  have h2 : cA D ε * cA D ε = cA D ε := by rw [← map_mul, he]
  have hs' : IsSplitIdem D (cA D ε) :=
    ⟨h2, by rw [cA_cA, mul_comm, hec], v, ε', hv, by rw [cA_cA, add_comm, heq]⟩
  have hε2 : IsSplitIdem D ε := ⟨he, hec, v, ε', hv, heq⟩
  obtain ⟨r, hr⟩ : ∃ r : AE D, r = 1 - ε - cA D ε := ⟨_, rfl⟩
  obtain ⟨h3, h13, h23, hsum, hr0⟩ := rest_idem he h2 hec hr
  have hkill : r • (Formalism.L2.Theta.mt T g - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) = 0 :=
    kill_of_supp hr0 hg'
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : AddSubgroup (WO S T), Λ = latO S T (frameLat S : Set (Fin S.rank → D.host.E))
    (frameLat T : Set (Fin T.rank → D.host.E)) fun _ => True := ⟨_, rfl⟩
  have hh : ∀ e, GlobalTheory.SplitIdx.halfLat S T e = Λ ⊓ half S T e := fun e => by rw [hΛ]; rfl
  have stε : ∀ a ∈ Λ, ε • a ∈ Λ := by
    rw [hΛ]
    exact fun a ha => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ ε (GlobalTheory.SplitHomLattice.idem_int hε2) a ha
  have stc : ∀ a ∈ Λ, cA D ε • a ∈ Λ := by
    rw [hΛ]
    exact fun a ha => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ (cA D ε) (GlobalTheory.SplitHomLattice.idem_int hs') a ha
  have str : ∀ a ∈ Λ, r • a ∈ Λ := fun a ha => by
    rw [hr, sub_smul, sub_smul, one_smul]
    exact sub_mem (sub_mem ha (stε a ha)) (stc a ha)

  have hL : GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T))
      ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, g))) =
      Λ.relIndex (Λ.map (GlobalTheory.SplitIdx.actL S T g)) := by
    have e1 : (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup = Λ.comap (XF.incl S T) :=
      AddSubgroup.ext fun _ => by rw [hΛ]; exact Iff.rfl
    have e2 : ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, g))).toAddSubgroup.map
        (XF.incl S T) = Λ.map (GlobalTheory.SplitIdx.actL S T g) := by
      refine AddSubgroup.ext fun u => ⟨?_, ?_⟩
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨(y : WO S T), ?_, rfl⟩
        rw [hΛ]
        exact hy
      · rintro ⟨w, hw, rfl⟩
        rw [hΛ] at hw
        exact ⟨GlobalTheory.FinWeilO.rhoF S T (1, g) (XF.mk w (latO_fin hw)), ⟨XF.mk w (latO_fin hw), hw, rfl⟩, rfl⟩
    rw [GlobalTheory.FinWeil.idx, e1, AddSubgroup.relIndex_comap, e2]
  rw [hh, hh, hL]
  exact split_index he h2 h3 hec h13 h23 hsum hkill stε stc str

end GlobalTheory.SplitIdxDec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothIntertwinerExtension
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.MatrixCoeffAgree

open scoped ContDiff

variable {n : ℕ} {ε : Fin n → Bool}

theorem exp_mem_UJset {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε :=
  GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) hX t

theorem exp_smul_add (X : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)

theorem hasDerivAt_orbit {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)} (hσ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) σ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {z : E}
    (h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) z) (dRep σ X z) 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) z) (σ (NormedSpace.exp (t • X)) (dRep σ X z)) t := by
  have h1 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s - t) • X)) z) (dRep σ X z) t := by
    have := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h0)
    exact this
  have h2 := ((σ (NormedSpace.exp (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [← ContinuousLinearMap.comp_apply, ← hσ.2 _ (exp_mem_UJset hX t) _ (exp_mem_UJset hX (s - t)),
    ← exp_smul_add]
  simp

theorem hasDerivAt_zero_of_smoothVec {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {z : E}
    (hz : Formalism.L2.Theta.SmoothVec (lieSet ε) σ z) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) z) (dRep σ X z) 0 := by
  have h1 := (hz 1 (fun _ => X) (fun _ => hX)).comp
    (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
  have h2 : ContDiff ℝ ∞ fun s : ℝ => σ (NormedSpace.exp (s • X)) z := by
    simpa [Function.comp_def] using h1
  exact ((h2.differentiable (by simp)) 0).hasDerivAt

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem differentiableAt_exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (t₀ : ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => NormedSpace.exp (s • X) a b) t₀ := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (t • X)) t₀ :=
    AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) (analyticAt_id.smul analyticAt_const)
  exact ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).differentiableAt).comp t₀
    h1.differentiableAt

end

theorem hasDerivAt_zero_of_smoothOnH {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {z : E}
    (hz : Formalism.QuantumDeterminants.SmoothOnH (Jm ε) fun g => σ g z) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) z) (dRep σ X z) 0 := by
  obtain ⟨U, F, hU, h0, hF, he⟩ := hz 1 (by simp [Formalism.QuantumDeterminants.inUH])
  let U' : Set (Fin n → Fin n → ℂ) := U
  let F' : (Fin n → Fin n → ℂ) → E := F
  have hU' : IsOpen U' := hU
  have hF' : ContDiffOn ℝ ∞ F' U' := hF
  let c : ℝ → (Fin n → Fin n → ℂ) := fun s => Matrix.of.symm (NormedSpace.exp (s • X) : Matrix (Fin n) (Fin n) ℂ)
  have hcd : DifferentiableAt ℝ c 0 :=
    differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => (differentiableAt_exp_entry X a b 0 :)
  have hc0 : c 0 = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [c, zero_smul, NormedSpace.exp_zero]
    rfl
  have hFd : DifferentiableAt ℝ F' (c 0) := by
    rw [hc0]
    exact (hF'.contDiffAt (hU'.mem_nhds h0)).differentiableAt (by simp)
  have hcomp := hFd.comp (0 : ℝ) hcd
  have hev : (fun s : ℝ => σ (NormedSpace.exp (s • X)) z) =ᶠ[nhds 0] F' ∘ c := by
    have : ∀ᶠ s in nhds (0 : ℝ), c s ∈ U' := by
      apply hcd.continuousAt.preimage_mem_nhds
      rw [hc0]
      exact hU'.mem_nhds h0
    filter_upwards [this] with s hs
    exact he _ hs (exp_mem_UJset hX s)
  exact (hcomp.congr_of_eventuallyEq hev).hasDerivAt

theorem eq_zero_of_iteratedDeriv {f : ℝ → ℂ} (hf : ∀ t, AnalyticAt ℝ f t)
    (h : ∀ k : ℕ, iteratedDeriv k f 0 = 0) (t : ℝ) : f t = 0 := by
  obtain ⟨p, r, hp⟩ := hf 0
  have hp0 : p = 0 := by
    ext k y
    have h1 := hp.factorial_smul 1 k
    rw [← iteratedDeriv_eq_iteratedFDeriv, h] at h1
    have h2 : p k (fun _ => 1) = 0 := by
      have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
      exact (smul_eq_zero.1 h1).resolve_left hk
    have h3 : p.coeff k = 0 := h2
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff, h3, smul_zero]
    rfl
  rw [hp0] at hp
  have hev : f =ᶠ[nhds 0] 0 := hp.hasFPowerSeriesAt.eventually_eq_zero
  exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero (U := Set.univ)
    (fun x _ => hf x) isPreconnected_univ (Set.mem_univ 0) hev (Set.mem_univ t)

section Main

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}

theorem one_mem_UJset : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  change (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
  simp

theorem coeff_exp_eq (hHC : GlobalTheory.Published.HarishChandraAnalyticity) (hρ : IsAdmRep ε ρ) (hπ : IsAdmRep ε π)
    (hGK : IsGKSub ε ρ (kFinVec ε ρ))
    (hsm : ∀ v, IsKFin ε π v → Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => π g v)) (T : H →ₗ[ℂ] V)
    (hT : ∀ y, IsKFin ε ρ y → IsKFin ε π (T y))
    (hL : ∀ X ∈ lieSet ε, ∀ y, IsKFin ε ρ y → T (dRep ρ X y) = dRep π X (T y)) {a : H} {w : V}
    (ha : IsKFin ε ρ a) (hw : IsKFin ε π w) (hpair : ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {y : H} (hy : IsKFin ε ρ y) (t : ℝ) :
    ⟪a, ρ (NormedSpace.exp (t • X)) y⟫_ℂ = ⟪w, π (NormedSpace.exp (t • X)) (T y)⟫_ℂ := by
  set G : H → ℝ → ℂ := fun z s =>
    ⟪a, ρ (NormedSpace.exp (s • X)) z⟫_ℂ - ⟪w, π (NormedSpace.exp (s • X)) (T z)⟫_ℂ with hGdef
  have hD : ∀ z, IsKFin ε ρ z → IsKFin ε ρ (dRep ρ X z) := fun z hz =>
    hGK.lieStable X hX z (mem_kFinVec.2 hz)
  have hderiv : ∀ z, IsKFin ε ρ z → ∀ s, HasDerivAt (G z) (G (dRep ρ X z) s) s := by
    intro z hz s
    have h1 := hasDerivAt_orbit hρ.1 hX (hasDerivAt_zero_of_smoothVec hX (hGK.smooth z (mem_kFinVec.2 hz))) s
    have h2 := hasDerivAt_orbit hπ.1 hX (hasDerivAt_zero_of_smoothOnH hX (hsm _ (hT z hz))) s
    have h1' := ((innerSL ℂ a).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    have h2' := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2
    have h3 := h1'.sub h2'
    simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at h3
    rw [hGdef]
    simp only
    rw [hL X hX z hz]
    exact h3
  have hiter : ∀ k z, IsKFin ε ρ z → iteratedDeriv k (G z) = G ((dRep ρ X)^[k] z) := by
    intro k
    induction k with
    | zero => intro z _; simp
    | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ', Function.iterate_succ_apply]
      have : deriv (G z) = G (dRep ρ X z) := funext fun s => (hderiv z hz s).deriv
      rw [this, ih _ (hD z hz)]
  have hkfin : ∀ k, IsKFin ε ρ ((dRep ρ X)^[k] y) := by
    intro k
    induction k with
    | zero => exact hy
    | succ k ih => rw [Function.iterate_succ_apply']; exact hD _ ih
  have hzero : ∀ z, IsKFin ε ρ z → G z 0 = 0 := by
    intro z hz
    simp only [hGdef, zero_smul, NormedSpace.exp_zero, hρ.1.1, hπ.1.1, ContinuousLinearMap.one_apply]
    rw [hpair z hz, sub_self]
  have han : ∀ s, AnalyticAt ℝ (G y) s := by
    intro s
    have h1 := (hHC.1 n ε H ρ hρ y a hy ha).analytic_exp one_mem_UJset hX s
    have h2 := (hHC.1 n ε V π hπ (T y) w (hT y hy) hw).analytic_exp one_mem_UJset hX s
    simp only [Matrix.one_mul] at h1 h2
    exact h1.sub h2
  have := eq_zero_of_iteratedDeriv han (fun k => by rw [hiter k y hy]; exact hzero _ (hkfin k)) t
  exact sub_eq_zero.1 this

end Main

theorem conj_mem_lieSet {k Y : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hY : Y ∈ lieSet ε) :
    k * Y * kᴴ ∈ lieSet ε := by
  have hY' : Yᴴ * Jm ε + Jm ε * Y = 0 := hY
  have hkJ : k * Jm ε = Jm ε * k := hk.2
  have hkJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    have := congrArg Matrix.conjTranspose hkJ
    simp only [Matrix.conjTranspose_mul, Jm_conjTranspose] at this
    exact this.symm
  change (k * Y * kᴴ)ᴴ * Jm ε + Jm ε * (k * Y * kᴴ) = 0
  calc (k * Y * kᴴ)ᴴ * Jm ε + Jm ε * (k * Y * kᴴ)
      = k * (Yᴴ * (kᴴ * Jm ε)) + (Jm ε * k) * Y * kᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = k * (Yᴴ * Jm ε + Jm ε * Y) * kᴴ := by
        rw [hkJ', ← hkJ]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY', Matrix.mul_zero, Matrix.zero_mul]

theorem mul_exp_eq {k Y : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k * NormedSpace.exp Y = NormedSpace.exp ((1 : ℝ) • (k * Y * kᴴ)) * k := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv h1
  have hu : IsUnit k := IsUnit.of_mul_eq_one_right _ h1
  rw [one_smul, ← hinv, Matrix.exp_conj k Y hu, Matrix.mul_assoc _ k⁻¹ k,
    Matrix.nonsing_inv_mul k ((Matrix.isUnit_iff_isUnit_det k).1 hu), Matrix.mul_one]

theorem matrixCoeff_eq : GlobalTheory.Published.HarishChandraAnalyticity → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsAdmRep ε ρ → IsAdmRep ε π → IsGKSub ε ρ (kFinVec ε ρ) → (∀ v, IsKFin ε π v → Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => π g v)) → ∀ T : H →ₗ[ℂ] V, (∀ y, IsKFin ε ρ y → IsKFin ε π (T y)) → (∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y)) → (∀ X ∈ lieSet ε, ∀ y, IsKFin ε ρ y → T (dRep ρ X y) = dRep π X (T y)) → ∀ (a : H) (w : V), IsKFin ε ρ a → IsKFin ε π w → (∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) → ∀ y, IsKFin ε ρ y → ∀ g ∈ UJset ε, ⟪a, ρ g y⟫_ℂ = ⟪w, π g (T y)⟫_ℂ := by
  intro hHC n ε H _ _ _ ρ V _ _ _ π hρ hπ hGK hsm T hT hK hL a w ha hw hpair y hy g hg
  obtain ⟨k, hk, Y, hY, rfl⟩ := ReciprocityTheory.ChartRestriction.DS.polar_UJ (show g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε from hg)
  have hk' : k ∈ Kset ε := hk
  have hYl : Y ∈ lieSet ε := hY.1
  have hZ := conj_mem_lieSet hk' hYl
  have hkU := GlobalTheory.GKModule.mem_UJset_of_mem_Kset hk'
  have hky : IsKFin ε ρ (ρ k y) := GlobalTheory.GKModule.isKStableOn_kFinVec ε ρ k hk' y hy
  rw [mul_exp_eq hk', hρ.1.2 _ (exp_mem_UJset hZ 1) _ hkU, hπ.1.2 _ (exp_mem_UJset hZ 1) _ hkU,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hK k hk' y hy]
  exact coeff_exp_eq hHC hρ hπ hGK hsm T hT hL ha hw hpair hZ hky 1

end GlobalTheory.MatrixCoeffAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralDefiniteSourceConvergesContinuousIn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.DefSourceInt

theorem theta_integral_source_definite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S W : HSp D) (χS χW : (AE D)ˣ →* Circle) (ω : WRep S W) (μ : Measure (GA D S)) (𝓕 : Set (GA D S)) (f : WO S W → ℂ), IsWeil ψ ε S W χS χW ω → (∀ τ, (gramAt D S τ).PosDef) → μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ → IsThetaFunO ψ (sgn ε S) W f → (∀ h, IntegrableOn (fun g => thetaKO ω g h f) 𝓕 μ) ∧ (Continuous fun h => ∫ g in 𝓕, thetaKO ω g h f ∂μ) ∧ ∀ γ ∈ GQ W, ∀ h, ∫ g in 𝓕, thetaKO ω g (γ * h) f ∂μ = ∫ g in 𝓕, thetaKO ω g h f ∂μ := by
  intro D ψ ε S W χS χW ω μ 𝓕 f hω hpos hμ h𝓕 hf
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  obtain ⟨hcont, hinv⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ (sgn ε S) W χS χW (WRep.toSgn ε ω) hω f hf
  have hK : ∀ g h, thetaKO ω g h f = thetaKO (WRep.toSgn ε ω) ((ofSgn ε S).symm g) h f := fun _ _ => rfl
  have hKc : Continuous fun p : GA D S × GA D W => thetaKO ω p.1 p.2 f :=
    (hcont.comp (((continuous_ofSgn_symm ε S).comp continuous_fst).prodMk continuous_snd)).congr fun p => (hK p.1 p.2).symm
  have hI : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ W, ∀ g h, thetaKO ω (γ * g) (γ' * h) f = thetaKO ω g h f := by
    intro γ hγ γ' hγ' g h
    rw [hK, hK, map_mul]
    exact hinv _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ ε hγ) γ' hγ' _ _
  have hIS : ∀ γ ∈ GQ S, ∀ g h, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI γ hγ 1 (one_mem _) g h
    rwa [one_mul] at this
  have hIW : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI 1 (one_mem _) γ hγ g h
    rwa [one_mul] at this
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  refine ⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain S μ 𝓕 C hμ h𝓕 hC hcov _
      (hKc.comp (Continuous.prodMk_left h)) (fun γ hγ g => hIS γ hγ g h)
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) μ 𝓕 C h𝓕 hC hcov
      (fun h g => thetaKO ω g h f) (hKc.comp continuous_swap) (fun γ hγ h g => hIS γ hγ g h)
  · have e : (fun g => thetaKO ω g (γ * h) f) = fun g => thetaKO ω g h f := funext fun g => hIW γ hγ g h
    exact congrArg (fun F : GA D S → ℂ => ∫ g in 𝓕, F g ∂μ) e

end GlobalTheory.DefSourceInt
end

