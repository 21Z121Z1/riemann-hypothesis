import Mathlib
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0667
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0366
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementA
section
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

namespace GlobalTheory.CompanionTheory.CTFin.IwaAd

theorem map_unip {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {a r : ℕ} (x : BlockIx a r → R) :
    GeneralLinearGroup.map f (unip x) = unip (fun p => f (x p)) := by
  apply Units.ext
  ext i j
  change f ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM (fun p => f (x p)) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

theorem map_lev {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (r s : ℕ)
    (m : GL (Fin r) R × GL (Fin s) R) :
    GeneralLinearGroup.map f (lev R r s m) =
      lev S r s (GeneralLinearGroup.map f m.1, GeneralLinearGroup.map f m.2) := by
  apply Units.ext
  ext i j
  change f (((lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) i j) = ((lev S r s _ : GL (Fin (r + s)) S) : Matrix _ _ S) i j
  rw [lev, lev, GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp

theorem exists_finset_cover (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Subgroup (GL (Fin n) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin n) (Af E)))) :
    ∃ T : Finset (GL (Fin n) (Af E)), ∀ c ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n,
      ∃ t ∈ T, ∃ l ∈ L, c = t * l := by
  obtain ⟨T, hT⟩ := (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).elim_finite_subcover
    (fun t : GL (Fin n) (Af E) => (fun z => t⁻¹ * z) ⁻¹' (L : Set (GL (Fin n) (Af E))))
    (fun t => hL.preimage (continuous_const.mul continuous_id))
    (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [L.one_mem]⟩)
  refine ⟨T, fun c hc => ?_⟩
  obtain ⟨t, ht, hl⟩ := Set.mem_iUnion₂.1 (hT hc)
  exact ⟨t, ht, t⁻¹ * c, hl, by group⟩

theorem iwasawa_finite_cosets : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∃ T : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GA E (r + s), ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E)) (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ T ∧ l ∈ L ∧ g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
  intro E _ _ _ r s L hL
  obtain ⟨T, hT⟩ := exists_finset_cover E (r + s) L hL
  refine ⟨T, fun g => ?_⟩
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (GeneralLinearGroup.map (pInf E) g)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) g)
  obtain ⟨t, ht, l, hl, rfl⟩ := hT c hc
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add, show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add, show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), t, k, l, ht, hl, ga_ext ?_ ?_⟩
  · simp only [map_mul, map_unip, map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [map_mul, map_unip, map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf, mul_assoc, mul_assoc, mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.IwaAd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnseenStatementBStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_unseen_statement_b : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₂ : Set (Module.End ℂ (Sm E s)), Cofin J₂ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ z ∈ J₂, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₂ : Subgroup (GL (Fin s) (Af E))) (ρ₂ : Representation ℂ (Kinf E s) W), IsOpen (L₂ : Set (GL (Fin s) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₂ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₁ : GA E r, ∃ G ∈ genSpace L₂ ρ₂ J₂, ∀ m₂ : GA E s, G.1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 | exact GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingCentralUnipotentCongruence
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.ZjContract

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic GroundTheory.Automorphic.GLnLocal
open GroundTheory.Automorphic.Iwasawa ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem diagGL_conj_mem {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α} {m : ℕ}
    (D : Fin n → kˣ)
    (hlt : ∀ i l, β i < β l → valuation k ((D i : k) * ((D l)⁻¹ : kˣ)) ≤ 1)
    (heq : ∀ i l, β i = β l → D i = D l)
    {u : GL (Fin n) k} (hu : u ∈ congruenceSubgroup k n m ⊓ unipotentRadical k n β) :
    diagGL k n D * u * (diagGL k n D)⁻¹ ∈
      congruenceSubgroup k n m ⊓ unipotentRadical k n β := by
  have hb : ∀ w ∈ congruenceSubgroup k n m ⊓ unipotentRadical k n β, ∀ i l,
      valuation k ((diagGL k n D * w * (diagGL k n D)⁻¹ : GL (Fin n) k) i l -
        (1 : Matrix (Fin n) (Fin n) k) i l) ≤
          valuation k ((uniformizer k : 𝒪[k]) : k) ^ m := by
    intro w hw i l
    obtain ⟨hwK, hwN⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨hwP, hw1⟩ := mem_unipotentRadical.1 hwN
    rw [diagGL_conj_apply]
    rcases lt_trichotomy (β i) (β l) with h | h | h
    · have hil : i ≠ l := fun e => h.ne (by rw [e])
      have hK := ((mem_congruenceSubgroup_iff k n).1 hwK).2 i l
      rw [one_apply_ne hil, sub_zero] at hK ⊢
      have e : (D i : k) * w i l * (((D l)⁻¹ : kˣ) : k) =
          ((D i : k) * (((D l)⁻¹ : kˣ) : k)) * w i l := by ring
      rw [e, map_mul]
      exact (mul_le_mul' (hlt i l h) hK).trans (by rw [one_mul])
    · rw [hw1 i l h, heq i l h]
      have : (D l : k) * (1 : Matrix (Fin n) (Fin n) k) i l * (((D l)⁻¹ : kˣ) : k) =
          (1 : Matrix (Fin n) (Fin n) k) i l := by
        rw [mul_right_comm, Units.mul_inv, one_mul]
      rw [this, sub_self, map_zero]
      exact zero_le
    · have hil : i ≠ l := fun e => h.ne' (by rw [e])
      have h0 : w i l = 0 := hwP h
      rw [h0, mul_zero, zero_mul, one_apply_ne hil, sub_zero, map_zero]
      exact zero_le
  have hP : diagGL k n D ∈ blockUpper k n β := levi_le_blockUpper (diagGL_mem_levi D)
  refine Subgroup.mem_inf.2 ⟨mem_congruenceSubgroup_of_le (hb u hu) ?_,
    conj_mem_unipotentRadical hP (Subgroup.mem_inf.1 hu).2⟩
  have : (diagGL k n D * u * (diagGL k n D)⁻¹)⁻¹ =
      diagGL k n D * u⁻¹ * (diagGL k n D)⁻¹ := by group
  rw [this]
  exact hb _ (Subgroup.inv_mem _ hu)

def zjDiag {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) : Fin N → kˣ :=
  fun i => if Zl.JC.blockIdx d hd i ≤ j then t else 1

theorem leviEmb_zj {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = diagGL k N (zjDiag d hd t j) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective x
  obtain ⟨⟨b, l⟩, rfl⟩ := (stdBlocks d hd).surjective y
  rw [coe_diagGL]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    have hb : Zl.JC.blockIdx d hd (stdBlocks d hd ⟨a, i⟩) = a := by simp [Zl.JC.blockIdx]
    by_cases hil : i = l
    · subst hil
      rw [diagonal_apply_eq]
      by_cases hj : a ≤ j
      · have hz : Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := if_pos hj
        have hD : zjDiag d hd t j (stdBlocks d hd ⟨a, i⟩) = t := by
          simp only [zjDiag, hb, if_pos hj]
        rw [hz, hD]
        simp
      · have hz : Zl.JC.zj d t j a = 1 := if_neg hj
        have hD : zjDiag d hd t j (stdBlocks d hd ⟨a, i⟩) = 1 := by
          simp only [zjDiag, hb, if_neg hj]
        rw [hz, hD]
        simp
    · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨a, l⟩ := fun e =>
        hil (by simpa using (stdBlocks d hd).injective e)
      rw [diagonal_apply_ne _ hne]
      by_cases hj : a ≤ j
      · have hz : Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := if_pos hj
        rw [hz]
        simp [hil]
      · have hz : Zl.JC.zj d t j a = 1 := if_neg hj
        rw [hz]
        simp [hil]
  · rw [leviEmb_apply_ne k _ _ hab, diagonal_apply_ne]
    intro e
    exact hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))

theorem zjDiag_ratio {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {t : kˣ}
    (ht : valuation k (t : k) ≤ 1) (j : Fin h) {i l : Fin N}
    (hil : Zl.JC.blockIdx d hd i < Zl.JC.blockIdx d hd l) :
    valuation k ((zjDiag d hd t j i : k) * (((zjDiag d hd t j l)⁻¹ : kˣ) : k)) ≤ 1 := by
  unfold zjDiag
  by_cases hi : Zl.JC.blockIdx d hd i ≤ j
  · by_cases hl : Zl.JC.blockIdx d hd l ≤ j
    · simp [if_pos hi, if_pos hl]
    · simpa [if_pos hi, if_neg hl] using ht
  · have hl : ¬ Zl.JC.blockIdx d hd l ≤ j := fun e => hi (hil.le.trans e)
    simp [if_neg hi, if_neg hl]

theorem zjDiag_eq {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) {i l : Fin N}
    (hil : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l) :
    zjDiag d hd t j i = zjDiag d hd t j l := by
  simp only [zjDiag, hil]

theorem zj_contract : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ), ValuativeRel.valuation k (t : k) ≤ 1 → ∀ (j : Fin h) (m : ℕ), (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd), leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * u * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)) ∧ (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd), (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ * z * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd)) := by
  intro k _ _ _ _ h N d hd t ht j m
  rw [leviEmb_zj]
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · exact diagGL_conj_mem _ (fun i l hil => zjDiag_ratio d hd ht j hil)
      (fun i l hil => zjDiag_eq d hd t j hil) hu
  · have key := diagGL_conj_mem (β := OrderDual.toDual ∘ Zl.JC.blockIdx d hd)
      (zjDiag d hd t j)⁻¹
      (fun i l hil => by
        have hil' : Zl.JC.blockIdx d hd l < Zl.JC.blockIdx d hd i := hil
        have := zjDiag_ratio d hd ht j hil'
        simpa [Pi.inv_apply, mul_comm] using this)
      (fun i l hil => by
        have hil' : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l := hil
        simp only [Pi.inv_apply, zjDiag_eq d hd t j hil'])
      (u := z) hz
    rw [map_inv, inv_inv] at key
    exact key

end GlobalTheory.CompanionTheory.ZjContract

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetMeasurable
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.ContractingCosets

open ValuativeRel Matrix GroundTheory.Automorphic.GLnLocal

theorem isOpen_doubleCoset {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (A : G) :
    IsOpen {g | ∃ x ∈ K, ∃ y ∈ K, g = x * A * y} := by
  have h : {g | ∃ x ∈ K, ∃ y ∈ K, g = x * A * y} =
      ⋃ x ∈ K, (fun y => x * A * y) '' (K : Set G) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    exact ⟨fun ⟨x, hx, y, hy, e⟩ => ⟨x, hx, y, hy, e.symm⟩,
      fun ⟨x, hx, y, hy, e⟩ => ⟨x, hx, y, hy, e.symm⟩⟩
  rw [h]
  exact isOpen_biUnion fun x _ => (Homeomorph.mulLeft (x * A)).isOpenMap _ hK

theorem eq_central_mul {G : Type*} [Group G] {x y x' y' A B : G}
    (hz : (x * A * y)⁻¹ * (x' * B * y') ∈ Subgroup.center G) :
    B = ((x * A * y)⁻¹ * (x' * B * y')) * ((x'⁻¹ * x) * A * (y * y'⁻¹)) := by
  have h := Subgroup.mem_center_iff.1 hz (x'⁻¹ * x * A * y)
  calc B = (x'⁻¹ * x * A * y) * ((x * A * y)⁻¹ * (x' * B * y')) * y'⁻¹ := by group
    _ = ((x * A * y)⁻¹ * (x' * B * y')) * (x'⁻¹ * x * A * y) * y'⁻¹ := by rw [h]
    _ = _ := by simp only [mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k]

theorem entry_bound {N : ℕ} {P Q B : Matrix (Fin N) (Fin N) k} {C : ValueGroupWithZero k}
    (hP : ∀ i j, valuation k (P i j) ≤ 1) (hQ : ∀ i j, valuation k (Q i j) ≤ 1)
    (hB : ∀ i j, valuation k (B i j) ≤ C) (i j : Fin N) :
    valuation k ((P * B * Q) i j) ≤ C :=
  _root_.UpperTheory.Reformulated.B.Ylb4.main hP hQ hB i j

theorem coe_pow_of_diag {N : ℕ} {δ : Fin N → k} {a : GL (Fin N) k}
    (ha : (a : Matrix (Fin N) (Fin N) k) = diagonal δ) (r : ℕ) :
    ((a ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = diagonal fun i => δ i ^ r := by
  rw [Units.val_pow_eq_pow_val, ha, diagonal_pow]
  rfl

theorem coe_inv_pow_of_diag {N : ℕ} {δ : Fin N → k} (hδ : ∀ i, δ i ≠ 0) {a : GL (Fin N) k}
    (ha : (a : Matrix (Fin N) (Fin N) k) = diagonal δ) (r : ℕ) :
    (((a ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = diagonal fun i => (δ i)⁻¹ ^ r := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [coe_pow_of_diag ha, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← mul_pow, mul_inv_cancel₀ (hδ i), one_pow]

theorem val_le_one_of_mem {N : ℕ} [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {g : GL (Fin N) k} (hg : g ∈ integralGL k N) (i j : Fin N) :
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (((mem_integralGL_iff k N).1 hg).1 i j)

theorem le_of_eq_central_mul {N : ℕ} [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ : Fin N → k} (t : kˣ) (ht : valuation k (t : k) < 1)
    (hδ : ∀ i, δ i = t ∨ δ i = 1) {i₁ i₂ : Fin N} (h₁ : δ i₁ = t) (h₂ : δ i₂ = 1)
    {a : GL (Fin N) k} (ha : (a : Matrix (Fin N) (Fin N) k) = diagonal δ)
    {p q z : GL (Fin N) k} (hp : p ∈ integralGL k N) (hq : q ∈ integralGL k N)
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) {r r' : ℕ}
    (h : a ^ r = z * (p * a ^ r' * q)) : r ≤ r' := by
  have hδ0 : ∀ i, δ i ≠ 0 := fun i => by
    rcases hδ i with h | h <;> rw [h]
    · exact t.ne_zero
    · exact one_ne_zero
  have hvt0 : valuation k (t : k) ≠ 0 := (Valuation.ne_zero_iff _).2 t.ne_zero
  have hvt1 : 1 ≤ (valuation k (t : k))⁻¹ := (one_lt_inv₀ (zero_lt_iff.2 hvt0)).2 ht |>.le
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  obtain ⟨c', hc'⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1
    (inv_mem hz)
  have hcc : c * c' = 1 := by
    have e := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i₂ i₂)
      (mul_inv_cancel z)
    simp only [Units.val_mul, ← hc, ← hc', Units.val_one] at e
    simpa [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] using e

  have hB : ∀ i j, valuation k (((a ^ r' : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ≤ 1 := by
    intro i j
    rw [coe_pow_of_diag ha]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, map_pow]
      refine pow_le_one₀ zero_le' ?_
      rcases hδ i with h | h <;> rw [h]
      · exact ht.le
      · simp
    · rw [diagonal_apply_ne _ hij]; simp

  have hB' : ∀ i j, valuation k ((((a ^ r')⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ≤
      (valuation k (t : k))⁻¹ ^ r' := by
    intro i j
    rw [coe_inv_pow_of_diag hδ0 ha]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, map_pow, map_inv₀]
      rcases hδ i with h | h <;> rw [h]
      simpa using one_le_pow₀ hvt1
    · rw [diagonal_apply_ne _ hij]; simp

  have hc1 : 1 ≤ valuation k c := by
    have e := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i₂ i₂) h
    simp only [Units.val_mul (a := z), ← hc] at e
    rw [coe_pow_of_diag ha, diagonal_apply_eq, h₂, one_pow, Matrix.scalar_apply,
      Matrix.diagonal_mul] at e
    have b := entry_bound (val_le_one_of_mem hp) (val_le_one_of_mem hq) hB i₂ i₂
    have e' := congrArg (valuation k) e
    rw [map_one, map_mul] at e'
    rw [Units.val_mul, Units.val_mul] at e'
    calc (1 : ValueGroupWithZero k) = _ := e'
      _ ≤ valuation k c * 1 := by gcongr
      _ = valuation k c := mul_one _
  have hc'1 : valuation k c' ≤ 1 := by
    have e : valuation k c * valuation k c' = 1 := by rw [← map_mul, hcc, map_one]
    calc valuation k c' = 1 * valuation k c' := (one_mul _).symm
      _ ≤ valuation k c * valuation k c' := by gcongr
      _ = 1 := e

  have hinv : (a ^ r)⁻¹ = (q⁻¹ * (a ^ r')⁻¹ * p⁻¹) * z⁻¹ := by
    rw [h]; group
  have hle : (valuation k (t : k))⁻¹ ^ r ≤ (valuation k (t : k))⁻¹ ^ r' := by
    have e := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i₁ i₁) hinv
    simp only [Units.val_mul (b := z⁻¹), ← hc'] at e
    rw [coe_inv_pow_of_diag hδ0 ha, diagonal_apply_eq, h₁, Matrix.scalar_apply,
      Matrix.mul_diagonal] at e
    have b := entry_bound (val_le_one_of_mem (inv_mem hq)) (val_le_one_of_mem (inv_mem hp)) hB' i₁ i₁
    have e' := congrArg (valuation k) e
    rw [map_pow, map_inv₀, map_mul, Units.val_mul, Units.val_mul] at e'
    rw [e']
    calc _ ≤ (valuation k (t : k))⁻¹ ^ r' * 1 := by gcongr
      _ = _ := mul_one _
  exact (pow_le_pow_iff_right₀ ((one_lt_inv₀ (zero_lt_iff.2 hvt0)).2 ht)).1 hle

theorem coe_leviEmb_zj {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) : Matrix (Fin N) (Fin N) k) =
      diagonal fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1 := by
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective x
  obtain ⟨⟨b, l⟩, rfl⟩ := (stdBlocks d hd).surjective y
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hil : i = l
    · subst hil
      rw [diagonal_apply_eq]
      simp only [Zl.JC.zj, Zl.JC.blockIdx, Equiv.symm_apply_apply]
      split_ifs <;> simp
    · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨a, l⟩ := fun e =>
        hil (by simpa using (stdBlocks d hd).injective e)
      rw [diagonal_apply_ne _ hne]
      simp only [Zl.JC.zj]
      split_ifs
      · simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, diagonal_apply_ne _ hil]
      · simp [Matrix.one_apply_ne hil]
  · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨b, l⟩ := fun e =>
      hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))
    rw [diagonal_apply_ne _ hne, leviEmb_apply_ne k _ _ hab]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem le_of_mk_eq {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hpos : ∀ a, 0 < d a) (t : kˣ)
    (ht : valuation k (t : k) < 1) (j : Fin h) (hj : j.val + 1 < h) (m : ℕ)
    {x y x' y' : GL (Fin N) k} (hx : x ∈ congruenceSubgroup k N m)
    (hy : y ∈ congruenceSubgroup k N m) (hx' : x' ∈ congruenceSubgroup k N m)
    (hy' : y' ∈ congruenceSubgroup k N m) {r r' : ℕ}
    (e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
      QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y')) :
    r' ≤ r := by
  have hz := QuotientGroup.eq.1 e
  have hK := congruenceSubgroup_le k N m
  have heq := eq_central_mul hz
  refine le_of_eq_central_mul (δ := fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1) t ht
    (fun i => ?_) (i₁ := stdBlocks d hd ⟨j, ⟨0, hpos j⟩⟩)
    (i₂ := stdBlocks d hd ⟨⟨j.val + 1, hj⟩, ⟨0, hpos _⟩⟩) ?_ ?_
    (coe_leviEmb_zj d hd t j)
    (mul_mem (inv_mem (hK hx')) (hK hx)) (mul_mem (hK hy) (inv_mem (hK hy'))) hz heq
  · by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  · simp [Zl.JC.blockIdx]
  · have : ¬ (⟨j.val + 1, hj⟩ : Fin h) ≤ j := by
      rw [Fin.le_def]; simp
    simp [Zl.JC.blockIdx, this]

theorem images_measurable_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)], (∀ r : ℕ, MeasurableSet ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y})) ∧ Pairwise (Function.onFun Disjoint fun r : ℕ => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  intro k _ _ _ _ h N d hd hpos t ht j hj m _ _ _
  refine ⟨fun r => ?_, fun r r' hne => ?_⟩
  · exact (QuotientGroup.isOpenMap_coe _
      (isOpen_doubleCoset _ (isOpen_congruenceSubgroup k N m) _)).measurableSet
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, e₁⟩ ⟨_, ⟨x', hx', y', hy', rfl⟩, e₂⟩
    have e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
        QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y') :=
      e₁.trans e₂.symm
    exact hne (le_antisymm (le_of_mk_eq d hd hpos t ht j hj m hx' hy' hx hy e.symm)
      (le_of_mk_eq d hd hpos t ht j hj m hx hy hx' hy' e))

end GlobalTheory.CompanionTheory.ContractingCosets

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingUnitAbsPowBounds
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.TopNilp

theorem nabs_absPow_of_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → 0 < nabs k t ∧ nabs k t < 1 ∧ ∀ d : ℕ, ‖((absPow k (d : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ d := by
  intro k _ _ _ _ t ht
  have hpos : 0 < nabs k t := nabs_pos' k t
  refine ⟨hpos, ?_, fun d => ?_⟩
  · by_contra hge
    have h1 : valuation k ((1 : kˣ) : k) ≤ valuation k (t : k) :=
      (nabs_le_iff 1 t).1 (by rw [nabs_one k]; exact not_lt.1 hge)
    rw [Units.val_one, map_one] at h1
    obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    have hr0 : r ≠ 0 := by simpa using hr
    have hnh : cball (Units.mk0 r hr0) ∈ 𝓝 (0 : k) :=
      (isOpen_cball _).mem_nhds (by simp [cball])
    obtain ⟨n, hn⟩ := (ht.eventually hnh).exists
    have h2 : valuation k ((t : k) ^ n) ≤ valuation k r := hn
    rw [map_pow] at h2
    exact absurd ((one_le_pow₀ h1).trans h2) (not_le.2 hr1)
  · rw [val_absPow, Complex.cpow_natCast, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos.le]

end GlobalTheory.CompanionTheory.TopNilp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleSurjectionFactorStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosocle_surjection_factor : ∀ {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V) (Q : Representation ℂ G X) (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (f : P.IntertwiningMap Q) (hf : Function.Surjective f) (hQ : Nontrivial X), ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  first | exact @GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient | exact GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient | (intros; apply GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjectiveStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_twist_injective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (hx : x.IsCusp) (a b : ℕ) (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  first | exact @GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | exact GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | (intros; apply GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactorStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equiv_of_multiplicity_one_unique_factor : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (T : Representation ℂ G W) (J : Representation ℂ G V), T.IsIrreducible → HasFiniteLength J → jhMult T J = 1 → (∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X), ρ.IsIrreducible → IsSubquotient ρ J → Nonempty (ρ.Equiv T)) → Nonempty (J.Equiv T) := by
  first | exact @GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one | exact GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one | (intros; apply GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZeroStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_pow_tendsto_zero' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∃ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) := by
  first | exact @GlobalTheory.CompanionTheory.LocalFieldPow.exists_unit_pow_tendsto_zero | exact GlobalTheory.CompanionTheory.LocalFieldPow.exists_unit_pow_tendsto_zero | (intros; apply GlobalTheory.CompanionTheory.LocalFieldPow.exists_unit_pow_tendsto_zero <;> assumption)
end

