import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.Bundle0013
import Formalism.LocalToGlobal.Columns.RowFormsAdelic
import Formalism.LocalToGlobal.Columns.Bundle0012
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.IsFDiagIffDiagonal
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0395
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricTypeRCMulInvMem
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ParGroup

variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

def InW (x : F) : Prop := ∃ o ∈ O, x = ϖ * o

theorem inW_sum {ι : Type} (s : Finset ι) (f : ι → F) (h : ∀ i ∈ s, InW O ϖ (f i)) :
    InW O ϖ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, O.zero_mem, by simp⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨o₁, ho₁, e₁⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨o₂, ho₂, e₂⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨o₁ + o₂, O.add_mem ho₁ ho₂, by rw [e₁, e₂, mul_add]⟩

theorem inW_mul_right {x a : F} (hx : InW O ϖ x) (ha : a ∈ O) : InW O ϖ (x * a) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨o * a, O.mul_mem ho ha, by ring⟩

theorem inW_mul_left {x a : F} (ha : a ∈ O) (hx : InW O ϖ x) : InW O ϖ (a * x) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨a * o, O.mul_mem ha ho, by ring⟩

theorem mul_mem_parJ {r c : ℕ} {k k' : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c)
    (hk' : k' ∈ parJ O ϖ r c) : k * k' ∈ parJ O ϖ r c := by
  obtain ⟨hkG, hkW⟩ := hk
  obtain ⟨hkG', hkW'⟩ := hk'
  refine ⟨(GLint O (r + c)).mul_mem hkG hkG', ?_⟩
  have hI : IsInt O (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.1
  have hI' : IsInt O (k' : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG'.1
  intro i j
  show InW O ϖ _
  simp only [bDA, Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply]
  apply inW_sum
  intro l _
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · exact inW_mul_right O ϖ (hkW i l) (hI' _ _)
  · exact inW_mul_left O ϖ (hI _ _) (hkW' l j)
private theorem lower_block_eq_zero_of_mul_eq_one {R : Type} [CommRing R] {r c : ℕ}
    (K N : Matrix (Fin (r + c)) (Fin (r + c)) R) (hKN : K * N = 1)
    (hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) = 0) (i : Fin c) (j : Fin r) :
    N (Fin.natAdd r i) (Fin.castAdd c j) = 0 := by
  let D : Matrix (Fin c) (Fin c) R := K.submatrix (Fin.natAdd r) (Fin.natAdd r)
  let T : Matrix (Fin c) (Fin c) R := N.submatrix (Fin.natAdd r) (Fin.natAdd r)
  let S : Matrix (Fin c) (Fin r) R := N.submatrix (Fin.natAdd r) (Fin.castAdd c)
  have key : ∀ a b, (K * N) (Fin.natAdd r a) b =
      ∑ l : Fin c, K (Fin.natAdd r a) (Fin.natAdd r l) * N (Fin.natAdd r l) b := by
    intro a b
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp [hK]
  have hDT : D * T = 1 := by
    ext a b
    have h := key a (Fin.natAdd r b)
    rw [hKN] at h
    simp only [D, T, Matrix.mul_apply, Matrix.submatrix_apply]
    rw [← h]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : Fin.natAdd r a ≠ Fin.natAdd r b := by
        intro e
        apply hab
        ext
        have := congrArg Fin.val e
        simp at this
        omega
      rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]
  have hDS : D * S = 0 := by
    ext a b
    have h := key a (Fin.castAdd c b)
    rw [hKN] at h
    have hne : Fin.natAdd r a ≠ Fin.castAdd c b := by
      intro e
      have := congrArg Fin.val e
      have hb := b.isLt
      simp at this
      omega
    rw [Matrix.one_apply_ne hne] at h
    simp only [D, S, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    exact h.symm
  have hTD : T * D = 1 := by
    first
    | exact mul_eq_one_comm.mp hDT
    | rw [← Matrix.inv_eq_right_inv hDT]
      exact Matrix.nonsing_inv_mul D (Matrix.isUnit_det_of_right_inverse hDT)
  have hS : S = 0 := by
    calc S = (T * D) * S := by rw [hTD, Matrix.one_mul]
      _ = T * (D * S) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hDS, Matrix.mul_zero]
  exact congrFun (congrFun hS i) j

theorem inv_mem_parJ {r c : ℕ} {k : GL (Fin (r + c)) F} (hϖ : ϖ ∈ O) (hk : k ∈ parJ O ϖ r c) :
    k⁻¹ ∈ parJ O ϖ r c := by
  obtain ⟨hkG, hkW⟩ := hk
  refine ⟨(GLint O (r + c)).inv_mem hkG, ?_⟩
  have hI : IsInt O (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.1
  have hJ : IsInt O ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.2
  let KO : Matrix (Fin (r + c)) (Fin (r + c)) O := fun a b => ⟨(k : Matrix (Fin (r + c)) (Fin (r + c)) F) a b, hI a b⟩
  let NO : Matrix (Fin (r + c)) (Fin (r + c)) O :=
    fun a b => ⟨((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) a b, hJ a b⟩
  have hKN : KO * NO = 1 := by
    apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have e1 : KO.map O.subtype = (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := by ext; rfl
    have e2 : NO.map O.subtype = ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) := by ext; rfl
    rw [e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let π := Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})
  have hKNb : KO.map π * NO.map π = 1 := by
    rw [← Matrix.map_mul, hKN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK0 : ∀ i j, KO.map π (Fin.natAdd r i) (Fin.castAdd c j) = 0 := by
    intro i j
    obtain ⟨o, ho, e⟩ := hkW i j
    rw [Matrix.map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    simp only [bDA, Matrix.submatrix_apply] at e
    simp only [KO, Subring.coe_mul, e]
    ring
  intro i j
  have h0 := lower_block_eq_zero_of_mul_eq_one (KO.map π) (NO.map π) hKNb hK0 i j
  rw [Matrix.map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
  obtain ⟨⟨o, ho⟩, e⟩ := h0
  refine ⟨o, ho, ?_⟩
  have e' := congrArg Subtype.val e
  simp only [NO, Subring.coe_mul] at e'
  simp only [bDA, Matrix.submatrix_apply]
  rw [← e']
  ring

theorem parJ_mul_inv : ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) F),
    k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c → k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c := by
  intro F _ O ϖ hϖ r c k k' hk hk'
  exact ⟨mul_mem_parJ O ϖ hk hk', inv_mem_parJ O ϖ hϖ hk⟩

end GlobalTheory.ParGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiLevelPairCompatibleOfColumnLevels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.PsiTie

theorem symPos_eq_symm {r k rS : ℕ} (hr : k + rS ≤ r) (i : Fin r) :
    symPos r rS k i = (Formalism.L2.Col.symPerm r k rS).symm i := by
  apply Fin.ext
  rw [Formalism.L2.Col.symPerm_symm_val hr]
  unfold symPos Formalism.L2.Col.symIdxInv
  have hi := i.2
  show (if i.val < rS then k + i.val else if i.val < rS + k then i.val - rS else i.val) % r = _
  rw [Nat.mod_eq_of_lt (by split_ifs <;> omega)]
  split_ifs <;> omega

theorem symPos_entries_iff {κ : Type} [CommRing κ] {r k rS : ℕ} (hr : k + rS ≤ r) (M y : GL (Fin r) κ) :
    (∀ i j : Fin r, (M : Matrix (Fin r) (Fin r) κ) (symPos r rS k i) (symPos r rS k j) =
      (y : Matrix (Fin r) (Fin r) κ) i j) ↔ Formalism.L2.Col.toSymOrd κ r k rS M = y := by
  simp only [symPos_eq_symm hr]
  constructor
  · intro h
    exact Units.ext (Matrix.ext fun i j => by rw [Formalism.L2.Col.toSymOrd_val]; exact h i j)
  · rintro rfl i j
    rfl

theorem baseLevel_character_preserved_placewiseIdentity {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] {r : ℕ} {S T : Finset (Pl E)}
    (hT : T = S) (e : G0 S r ≃* G0 T r) (he : ∀ g P (h : P ∈ S) (h' : P ∈ T), e g ⟨P, h'⟩ = g ⟨P, h⟩)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) :
    (∀ g, g ∈ (P0 S r ψ).H ↔ e g ∈ (P0 T r ψ).H) ∧
      ∀ (g : (P0 S r ψ).H) (h : e g ∈ (P0 T r ψ).H), (P0 S r ψ).chi g = (P0 T r ψ).chi ⟨e g, h⟩ := by
  subst hT
  have hid : ∀ g, e g = g := fun g => funext fun P => he g P.1 P.2 P.2
  refine ⟨fun g => by rw [hid], fun g h => ?_⟩
  exact congrArg _ (Subtype.ext (hid g).symm)

theorem piChar_apply' {K : Type} [Field K] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))
    (lam : ∀ i, ↥(H i) →* Kˣ) (x : ↥(Subgroup.pi Set.univ H)) :
    Formalism.L2.Col.piChar H lam x = ∏ i, lam i (Formalism.L2.Col.piProj H i x) :=
  MonoidHom.finset_prod_apply _ _ _

theorem ofLocal_chi_apply {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] {r : ℕ} {Pg : Finset (Pl E)}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* LLˣ) (x : ↥(Subgroup.pi Set.univ Hl)) :
    (LevelP.ofLocal Hl cl).chi x = ∏ PP, cl PP (LevelP.prj Hl PP x) :=
  MonoidHom.finset_prod_apply _ _ _

theorem sym_tie {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m)
    {T : Finset (Pl X.E)} (hT : T = Pr.vGs) (e : Formalism.L2.Col.G0 X.E Pr.vGs R.r ≃* G0 T R.r)
    (he : ∀ g P (h : P ∈ Pr.vGs) (h' : P ∈ T), e g ⟨P, h'⟩ = g ⟨P, h⟩)
    (ψ : ∀ PP : Pl X.E, AddChar (kP PP) X.K) (hψ : ∀ P (h : P ∈ Pr.vGs), ψ P = Ch.psi0 ⟨P, h⟩) :
    (∀ g, g ∈ (Formalism.L2.Col.rPsymF Ch).grp ↔ ∃ y ∈ (PsharpSym T R.r R.rS R.k ψ).H, ∀ (PP : ↥T) (i j : Fin R.r),
      ((e g PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) (symPos R.r R.rS R.k i) (symPos R.r R.rS R.k j) =
        ((y PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) i j) ∧
    ∀ (g : (Formalism.L2.Col.rPsymF Ch).grp) (y : (PsharpSym T R.r R.rS R.k ψ).H), (∀ (PP : ↥T) (i j : Fin R.r),
      ((e g PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) (symPos R.r R.rS R.k i) (symPos R.r R.rS R.k j) =
        (((y : G0 T R.r) PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) i j) →
      (Formalism.L2.Col.rPsymF Ch).chr g = (PsharpSym T R.r R.rS R.k ψ).chi y := by
  subst hT
  have hid : ∀ g, e g = g := fun g => funext fun P => he g P.1 P.2 P.2
  have hr : R.k + R.rS ≤ R.r := by have := Formalism.L2.Col.r_eq_sym R; omega
  refine ⟨fun g => ?_, fun g y hgy => ?_⟩
  · rw [hid]
    constructor
    · intro hg
      refine ⟨fun PP => Formalism.L2.Col.toSymOrd _ R.r R.k R.rS (g PP), (Subgroup.mem_pi _).2 fun PP _ => ?_,
        fun PP => (symPos_entries_iff hr _ _).2 rfl⟩
      have := (Subgroup.mem_pi _).1 hg PP (Set.mem_univ _)
      change g PP ∈ Formalism.L2.Col.HPsymF _ R.r R.k R.rS at this
      rw [Formalism.L2.Col.HPsymF_eq_comap_unipSym, Subgroup.mem_comap] at this
      exact this
    · rintro ⟨y, hy, hyg⟩
      refine (Subgroup.mem_pi _).2 fun PP _ => ?_
      change g PP ∈ Formalism.L2.Col.HPsymF _ R.r R.k R.rS
      rw [Formalism.L2.Col.HPsymF_eq_comap_unipSym, Subgroup.mem_comap, (symPos_entries_iff hr _ _).1 (hyg PP)]
      exact (Subgroup.mem_pi _).1 hy PP (Set.mem_univ _)
  · rw [hid] at hgy
    have h1 := piChar_apply' (fun w => (Formalism.L2.Col.rPsymF Ch w).H) (fun w => (Formalism.L2.Col.rPsymF Ch w).lam) g
    have h2 := ofLocal_chi_apply (fun PP : ↥Pr.vGs => unipSym (kP PP.1) R.r R.rS R.k)
      (fun PP => addCharHom (ψ PP.1) (symHom (kP PP.1) R.r R.rS R.k)) y
    refine h1.trans (Eq.trans ?_ h2.symm)
    refine Finset.prod_congr rfl fun w _ => ?_
    have hy : (y : G0 Pr.vGs R.r) w = Formalism.L2.Col.toSymOrd _ R.r R.k R.rS ((g : Formalism.L2.Col.G0 X.E Pr.vGs R.r) w) :=
      ((symPos_entries_iff hr _ _).1 (hgy w)).symm
    have hM : Formalism.L2.Col.toSymOrd _ R.r R.k R.rS ((g : Formalism.L2.Col.G0 X.E Pr.vGs R.r) w) ∈ unipSym (kP w.1) R.r R.rS R.k := by
      rw [← hy]; exact (Subgroup.mem_pi _).1 y.2 w (Set.mem_univ _)
    apply Units.ext
    have e1 := Formalism.L2.Col.chiSym_eq_symHom (Ch.psi0 w) R.r R.k R.rS
      ⟨_, Formalism.L2.Col.mem_HPsymF.1 ((Subgroup.mem_pi _).1 g.2 w (Set.mem_univ _))⟩ hM
    refine e1.trans ?_
    rw [hψ w.1 w.2]
    congr 2
    exact Subtype.ext hy.symm

theorem psiPPTie_of_levOf : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) → (∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) → PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) := by
  intro X px I U L eG cG plg iso hOk hLev hId hpl hbc
  have hψ : ∀ P (h : P ∈ (X.B.primes px).vGs), psiC I P = I.Ch.psi0 ⟨P, h⟩ := fun P h => psiC_of_mem I h
  have hP0 := baseLevel_character_preserved_placewiseIdentity (S := (X.B.primes px).vGs) hLev.Pg eG (fun g P h h' => hId g P h h') (psiC I)
  have hS := sym_tie I.Ch hLev.Pg eG (fun g P h h' => hId g P h h') (psiC I) hψ
  refine ⟨L.Pg, plg, fun kv => (iso kv).symm, psiC I, eG, ?_, ?_⟩
  · refine ⟨hpl, ?_, ?_, hP0.1, hP0.2, hS.1, hS.2⟩
    · intro g kv
      rw [hbc g kv]
      apply Units.ext
      ext i j
      simp [Matrix.GeneralLinearGroup.map, Formalism.UG.bc]
    · intro PP hPP
      rw [hLev.Pg] at hPP
      rw [psiC_of_mem I hPP]
      exact hOk.ch_ok.psi_zero_nontrivial_character _
  · intro kv c b hb
    have hw : ((plg kv : L.Pg) : Pl X.toD7.host.E) ∈ (X.B.primes px).vGs := hLev.Pg ▸ (plg kv).2
    have h := hOk.weil ⟨_, hw⟩ c b hb
    rw [psiC_of_mem I hw]
    refine h.trans ?_
    have hq : Formalism.L2.Col.qOf ((⟨_, hw⟩ : {w // w ∈ (X.B.primes px).vGs}) : Pl X.B.fields.E) = X.toD7.host.g kv.1 :=
      absNorm_eq_of_res X.toD7 (iso kv).symm
    rw [hq]

end GlobalTheory.Mem.PsiTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
section
noncomputable section

open scoped TensorProduct

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowAd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (X : Stages)

theorem rank_X' : X.toD7.sp.X'.rank = X.B.R.N X.B.R.m - 1 := by
  rw [X.toD7.sp.X'_rank, Formalism.L2.Col.rank_X'_eq]
  rfl

def ptE (h : Bridge.Gf X.toD7.sp.X') :
    GL (Fin (X.B.R.N X.B.R.m - 1)) (X.B.fields.E ⊗[X.B.fields.F] Formalism.L2.Herm.Af X.B.fields.F) :=
  Units.map (Matrix.reindexAlgEquiv (Formalism.IndefR.Lev.EAf X.toD7) (Formalism.IndefR.Lev.EAf X.toD7) (finCongr (rank_X' X))).toMonoidHom
    (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE X.toD7) h.1)

variable {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) {U : Set I.ι}

def decoAd (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).D :=
  Formalism.L2.Col.decoOf (F := X.B.fields.F) (E := X.B.fields.E) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (ptE X h)

def ReadsDeco (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (cX : CoefA X.toD7.sp.X') {J : Subgroup (Bridge.Gf X.toD7.sp.X')}
    {χ : J →* ℂˣ} (t : TupU I U)
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ) : Prop :=
  ∃ m : ((famR X I hX U Xg tr).A.MtildeCSD t).V →ₛₗ[X.toD7.what₂.embLL] cX.W,
    ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'),
      P.ext (f : _ → _) h = m ((((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1
        (decoAd X I t h))

end GlobalTheory.Mem.R3.RowAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsLiftsHeckeOperatorsCommute
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

open Formalism.L2.Col Formalism.HermitianLatticesTheory

namespace GlobalTheory.InertSame

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem sameAt_trans {Q : HeightOneSpectrum (𝓞 E)} {A B C : Submodule (𝓞 E) (Sp E n)}
    (h1 : SameAt Q A B) (h2 : SameAt Q B C) : SameAt Q A C := by
  obtain ⟨a, ha, a', ha', h1, h1'⟩ := h1
  obtain ⟨b, hb, b', hb', h2, h2'⟩ := h2
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]; exact h1 _ (h2 x hx)
  · rw [mul_smul]; exact h2' _ (h1' x hx)

theorem sameAt_refl (Q : HeightOneSpectrum (𝓞 E)) (A : Submodule (𝓞 E) (Sp E n)) : SameAt Q A A :=
  ⟨1, fun h => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), 1,
    fun h => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩

theorem paths_equiv (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P = P) (hin : ∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal)
    (X Z : Submodule (𝓞 E) (Sp E n)) (hX : Submodule.IsLattice E X) (hZ : Submodule.IsLattice E Z)
    (hXu : IsUnimodular (hStd E n) X) (hZu : IsUnimodular (hStd E n) Z) (s t : List ℕ) :
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s X Y ∧ IsInertNbr P.asIdeal t Y Z} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t X Y ∧ IsInertNbr P.asIdeal s Y Z}) := by
  by_cases hXZ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Z
  · obtain ⟨σ, hσX, hσZ, hgood, hsurj, hinj, hrel⟩ := GlobalTheory.T.exists_local_unitary_exchange_unimodular_lattices_inert P hP hin X Z hX hZ hXu hZu hXZ
    have gX : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X X := fun Q _ => sameAt_refl Q X
    have away : ∀ {u : List ℕ} {Y : Submodule (𝓞 E) (Sp E n)}, IsInertNbr P.asIdeal u X Y →
        ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y := fun h Q hQ => hi_sameAt_inert hQ h
    have fwd : ∀ Y : {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s X Y ∧ IsInertNbr P.asIdeal t Y Z},
        Submodule.IsLattice E (σ Y.1) ∧ IsUnimodular (hStd E n) (σ Y.1) ∧
          IsInertNbr P.asIdeal t X (σ Y.1) ∧ IsInertNbr P.asIdeal s (σ Y.1) Z := by
      rintro ⟨Y, hl, hu, h1, h2⟩
      obtain ⟨gl, gu, -⟩ := hgood Y hl hu (away h1)
      have r1 := (hrel s X Y hX hXu gX hl hu (away h1)).2 h1
      have r2 := (hrel t Y Z hl hu (away h1) hZ hZu hXZ).2 h2
      rw [hσX] at r1
      rw [hσZ] at r2
      exact ⟨gl, gu, r2.symm, r1.symm⟩
    refine ⟨Equiv.ofBijective (fun Y => ⟨σ Y.1, fwd Y⟩) ⟨?_, ?_⟩⟩
    · rintro ⟨Y, hl, hu, h1, h2⟩ ⟨Y', hl', hu', h1', h2'⟩ he
      have := congrArg Subtype.val he
      exact Subtype.ext (hinj Y Y' hl hu (away h1) hl' hu' (away h1') this)
    · rintro ⟨Y', hl', hu', h1', h2'⟩
      obtain ⟨Y, hl, hu, ha, rfl⟩ := hsurj Y' hl' hu' (away h1')
      refine ⟨⟨Y, hl, hu, ?_, ?_⟩, rfl⟩
      · refine (hrel s X Y hX hXu gX hl hu ha).1 ?_
        rw [hσX]
        exact h2'.symm
      · refine (hrel t Y Z hl hu ha hZ hZu hXZ).1 ?_
        rw [hσZ]
        exact h1'.symm
  · have e1 : IsEmpty {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s X Y ∧ IsInertNbr P.asIdeal t Y Z} :=
      ⟨fun Y => hXZ fun Q hQ => sameAt_trans (hi_sameAt_inert hQ Y.2.2.2.1) (hi_sameAt_inert hQ Y.2.2.2.2)⟩
    have e2 : IsEmpty {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t X Y ∧ IsInertNbr P.asIdeal s Y Z} :=
      ⟨fun Y => hXZ fun Q hQ => sameAt_trans (hi_sameAt_inert hQ Y.2.2.2.1) (hi_sameAt_inert hQ Y.2.2.2.2)⟩
    exact ⟨Equiv.equivOfIsEmpty _ _⟩

section Ops
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

theorem heckeI_comm_same (c : DecoPts S E n ST SG) (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P = P)
    (hin : ∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) (hST : ∀ R : ST, R.1 ≠ P) (hSG : ∀ w : SG, w.1 ≠ P)
    (s t : List ℕ) : Commute (heckeI c P.asIdeal s).op (heckeI c P.asIdeal t).op := by
  classical
  refine hi_commute c _ _ _ _ (heckeI_op_apply' c _ s) (heckeI_op_apply' c _ t) fun d f => ?_
  exact GlobalTheory.T.inertPath_card_comm_latticePaths P hST hSG s t d f (paths_equiv P hP hin d.1.N f.1.N d.2.lat f.2.lat d.2.uni f.2.uni s t)

theorem heckeCommAll_all (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : HeckeCommAll c S0 :=
  heckeCommAll_of_same c S0 fun P s t => heckeI_comm_same c P.1 P.2.1 P.2.2.1
    (fun R => P.ne_of_mem (Or.inl (Or.inr R.2))) (fun w => P.ne_of_mem (Or.inr w.2)) s t
end Ops

end GlobalTheory.InertSame

namespace GlobalTheory.Mem.R3.Comm

theorem rows_lifts_comm : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → ∀ a : I.ι,
  Formalism.L2.Col.HeckeCommAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
    ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeCommAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ :=
  fun _ _ _ _ _ _ => ⟨GlobalTheory.InertSame.heckeCommAll_all _ _, fun _ => GlobalTheory.InertSame.heckeCommAll_all _ _⟩
end GlobalTheory.Mem.R3.Comm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameCfgRefl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.HFld

open Classical in

def chiC {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) :
    Fin B.R.m → IsDedekindDomain.HeightOneSpectrum (𝓞 B.host.E) → 𝓞 B.host.E → ℂ :=
  fun j w y =>
    if h : w ∈ (B.primes px).vGs then
      if hu : IsUnit (Ideal.Quotient.mk w.asIdeal y) then B.embLL ((I.Ch.chi j ⟨w, h⟩ hu.unit : B.LLˣ) : B.LL) else 0
    else 0

open Classical in

def qC {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) :
    Formalism.L2.Host.HChar B.host.E → Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 B.host.E)) :=
  fun ξ => if h : ∃ a, I.xi a = ξ then I.Q h.choose else ∅

def SameCfg (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px) (B' : Base) (px' : PreX B'.toPre) (I' : Col2.ColIn B' px') : Prop :=
  B.toPre = B'.toPre ∧ HEq I.C I'.C ∧ HEq (Set.range I.xi) (Set.range I'.xi) ∧ HEq px.piG px'.piG ∧ HEq (chiC I) (chiC I') ∧
    HEq (qC I) (qC I')

end GlobalTheory.Mem.HFld

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_lattices_diagonal : GlobalTheory.Mem.Top.Ev fun K => ∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame)) := by
  first | exact @GlobalTheory.Mem.HostFrames.hostHyp_frames_ev | exact GlobalTheory.Mem.HostFrames.hostHyp_frames_ev | (intros; apply GlobalTheory.Mem.HostFrames.hostHyp_frames_ev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidueStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameInertia_representative_residue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime], IsPlaceOver (F := E) A P → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g), σ ∈ Ine (F := E) A → IsGenSys ζ → TameCoupled A κ σ ζ → (∀ A' : ValuationSubring Ω, IsPlaceOver (F := E) A' P → σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A) → ∀ u : 𝓞 E, NX.TameRep P 1 σ u → ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧ algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  first | exact @GlobalTheory.tameRep_residue | exact GlobalTheory.tameRep_residue | (intros; apply GlobalTheory.tameRep_residue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftDefiniteConstantTermEqZeroStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_definite_constantTerm_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (∀ x h g ξ, IsoVec T ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin S.rank → AE D, ∑ k, heisO ψ S T (along S T ξ (a k)) (om (h, g) (L x)) = 0) → ZCusp T (lift om ν 𝓕 fun h => L (F h)) := by
  first | exact @GlobalTheory.DefLiftCusp.zcusp_lift | exact GlobalTheory.DefLiftCusp.zcusp_lift | (intros; apply GlobalTheory.DefLiftCusp.zcusp_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopSpacesMapOntoChainTopInCoordinatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSpaces_map_onto_chainTop_in_coordinates : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ jX : ∀ μ, (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX, (∀ μ, y.Us μ → Function.Injective (jX μ) ∧ LinearMap.range (jX μ) = (y.C F.lv2).CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = (y.C F.lv2).ipXP b μ (jX μ x) (jX μ x')) ∧ ∀ t, y.Us (y.tup t) → ∀ x, jX (y.tup t) (((tA (y.tup t)).cast (hA t)).j x) = R.toRealDat.cX.toMap R.toRealDat.prX ((R.toRealDat.HX t).e (R.toRealDat.jX t (rowForm A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t x))) := by
  first | exact @GlobalTheory.TopRead.top_read | exact GlobalTheory.TopRead.top_read | (intros; apply GlobalTheory.TopRead.top_read <;> assumption)
end

