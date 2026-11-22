import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartanExchangeUnimodularInertPrime
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLocalDensityStandardLatticeBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActRep
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultAction

theorem actRep : ∀ D : D7, ActRep D := by
  intro D V β L S θ M hl hP
  have e : Formalism.IndefR.Lev.flag1L L = L := by
    rw [flag1L, withP, ← hP]
  have hM : Mult θ M (levS V β L) (levChi V β L) = MultP θ M β L := by
    rw [MultP, e]
  rw [hM]
  refine ⟨fun g T hT => act_mem g hT, fun T hT => act_one hT, fun g h T hT => act_mul hl g h hT, ?_⟩
  intro G _ _ eG c hc g T hT
  have h := gaL_act eG hl (c := c) (fun a b => hc a b) (eG.symm g) hT
  rwa [MulEquiv.apply_symm_apply] at h

end GlobalTheory.MultAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_unimodular_exists_fundamentalDomain : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ ∃ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ := by
  first | exact @GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain | exact GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain | (intros; apply GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselCharacter_generic_character_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ d : BesDat A B ι, (∀ n n' : NFlag B d.e, besChar ψ d ((n * n' : NFlag B d.e) : GA D B) = besChar ψ d (n : GA D B) * besChar ψ d (n' : GA D B)) ∧ (∀ γ ∈ NFlagQ B d.e, besChar ψ d (γ : GA D B) = 1) ∧ (Continuous fun n : NFlag B d.e => besChar ψ d (n : GA D B)) ∧ ∀ g h, EmbRel B A ι g h → ∀ n ∈ NFlag B d.e, g * n * g⁻¹ ∈ NFlag B d.e ∧ besChar ψ d (g * n * g⁻¹) = besChar ψ d n := by
  first | exact @GlobalTheory.BesselChar.besChar_laws | exact GlobalTheory.BesselChar.besChar_laws | (intros; apply GlobalTheory.BesselChar.besChar_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def exF (d : BesselDatum A B ι) (ε : AE D) (i : Fin (d.ρ + 1)) (m : Measure (d.Ex ε i)) (β : GA D B → ℂ) :
    GA D B → ℂ := fun g => ∫ u, β ((u : GA D B) * g) ∂m

def toPosF (d : BesselDatum A B ι) (ε : AE D) (m : ∀ i, Measure (d.Ex ε i)) (p : ℕ) (β : GA D B → ℂ) : GA D B → ℂ :=
  ((List.finRange (d.ρ + 1)).filter fun i => decide (p ≤ i.1)).foldr (fun i β' => exF d ε i (m i) β') β

def moveF (P : PosDatum A B ι) (β : GA D B → ℂ) : GA D B → ℂ :=
  (List.finRange P.n).foldr (fun a β' => toPosF P.bes (P.ε a) (P.m a) (P.p a) β') β

def Lvl (β : GA D B → ℂ) : Prop :=
  ∃ U : Subgroup (GA D B), IsOpen (U : Set (GA D B)) ∧ ∀ k ∈ U, k ∈ GfC B → ∀ g, β (g * k) = β g

def Eqv (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (ε : AE D) (β : GA D B → ℂ) : Prop :=
  ∀ n ∈ d.N, SuppAt ε B n → ∀ g, β (n * g) = d.psiN ψ n * β g

def IsK (B : HSp D) (v y : Fin B.rank → AE D) (k : GA D B) : Prop :=
  ∀ x, (mt B k).mulVec x = x + hA B x y • v - hA B x v • y

def iA (ι : A.V →ₗ[D.host.E] B.V) (t : Fin A.rank → AE D) : Fin B.rank → AE D :=
  ((frameMat B A ι).map (incA D)).mulVec t

def dual (d : BesselDatum A B ι) : Fin (d.ρ + 1) → B.V :=
  Fin.snoc (α := fun _ => B.V) d.f ((B.hD d.z d.z)⁻¹ • d.z)

def ExGe (d : BesselDatum A B ι) (ε : AE D) (p : ℕ) : Subgroup (GA D B) :=
  Subgroup.closure (⋃ l : Fin (d.ρ + 1), ⋃ _ : p ≤ l.1, d.ExSet ε l)

theorem rTr_rTr (u g : GA D B) (F : GA D B → ℂ) : rTr B u (rTr B g F) = rTr B (u * g) F := by
  funext x; simp only [rTr, mul_assoc]

theorem rTr_one (F : GA D B → ℂ) : rTr B 1 F = F := by funext x; simp only [rTr, mul_one]

theorem toPos_rTr (d : BesselDatum A B ι) (ε : AE D) (m : ∀ i, Measure (d.Ex ε i)) (p : ℕ)
    (b : (GA D B → ℂ) → ℂ) (F : GA D B → ℂ) :
    (fun g => d.toPos ε m p b (rTr B g F)) = toPosF d ε m p fun g => b (rTr B g F) := by
  unfold BesselDatum.toPos toPosF
  induction (List.finRange (d.ρ + 1)).filter fun i => decide (p ≤ i.1) with
  | nil => rfl
  | cons i l ih =>
    funext g
    simp only [List.foldr_cons, BesselDatum.exch, exF, ← ih, rTr_rTr]

theorem move_rTr (P : PosDatum A B ι) (b : (GA D B → ℂ) → ℂ) (F : GA D B → ℂ) :
    (fun g => P.move b (rTr B g F)) = moveF P fun g => b (rTr B g F) := by
  unfold PosDatum.move moveF
  induction List.finRange P.n with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ← ih, toPos_rTr]

theorem cA_cA (a : AE D) : cA D (cA D a) = a := GlobalTheory.DualPairCheck.cA_cA a

theorem mt_inj {g h : GA D B} (e : mt B g = mt B h) : g = h := Subtype.ext (Units.ext e)

theorem mt_ext {g h : GA D B} (e : ∀ x, (mt B g).mulVec x = (mt B h).mulVec x) : g = h :=
  mt_inj (Matrix.mulVec_injective (funext e))

theorem mulVec_mul (g h : GA D B) (x) : (mt B (g * h)).mulVec x = (mt B g).mulVec ((mt B h).mulVec x) := by
  rw [mt_mul, Matrix.mulVec_mulVec]

theorem mulVec_inv_cancel (g : GA D B) (x) : (mt B g⁻¹).mulVec ((mt B g).mulVec x) = x := by
  rw [← mulVec_mul, inv_mul_cancel, mt_one, Matrix.one_mulVec]

theorem mulVec_cancel_inv (g : GA D B) (x) : (mt B g).mulVec ((mt B g⁻¹).mulVec x) = x := by
  rw [← mulVec_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]

theorem hA_eq (x y : Fin B.rank → AE D) : hA B x y = (fun i => cA D (y i)) ⬝ᵥ (B.gram.map (incA D)).mulVec x := by
  simp only [hA, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hA_herm (x y : Fin B.rank → AE D) : cA D (hA B x y) = hA B y x := by
  simp only [hA, map_sum, RingHom.map_mul, cA_inc, cA_cA, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hA_add_right (x y y' : Fin B.rank → AE D) : hA B x (y + y') = hA B x y + hA B x y' := by
  simp only [hA, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hA_neg (x y : Fin B.rank → AE D) : hA B (-x) y = -hA B x y := by
  simp only [hA, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hA_neg_right (x y : Fin B.rank → AE D) : hA B x (-y) = -hA B x y := by
  simp only [hA, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem hA_sub (x x' y : Fin B.rank → AE D) : hA B (x - x') y = hA B x y - hA B x' y := by
  rw [sub_eq_add_neg, hA_add, hA_neg, ← sub_eq_add_neg]

theorem hA_sub_right (x y y' : Fin B.rank → AE D) : hA B x (y - y') = hA B x y - hA B x y' := by
  rw [sub_eq_add_neg, hA_add_right, hA_neg_right, ← sub_eq_add_neg]

theorem hA_zero (y : Fin B.rank → AE D) : hA B 0 y = 0 := by simp [hA]

theorem hA_zero_right (x : Fin B.rank → AE D) : hA B x 0 = 0 := by simp [hA]

theorem hA_mt (g : GA D B) (x y : Fin B.rank → AE D) :
    hA B ((mt B g).mulVec x) ((mt B g).mulVec y) = hA B x y := by
  have hg : ((mt B g).map (cA D))ᵀ * B.gram.map (incA D) * mt B g = B.gram.map (incA D) := g.2
  have e : (fun i => cA D ((mt B g).mulVec y i)) = ((mt B g).map (cA D)).mulVec fun i => cA D (y i) :=
    funext fun i => RingHom.map_mulVec (cA D) _ y i
  rw [hA_eq, hA_eq, e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hg]

theorem hA_mt_left (g : GA D B) (x y : Fin B.rank → AE D) :
    hA B ((mt B g).mulVec x) y = hA B x ((mt B g⁻¹).mulVec y) := by
  rw [← hA_mt g x, mulVec_cancel_inv]

theorem hA_nondeg {x : Fin B.rank → AE D} (h : ∀ y, hA B x y = 0) : x = 0 := by
  have hu : IsUnit (B.gram.map (incA D)) := (GlobalTheory.BesselCompare.gram_isUnit B).map (incA D).mapMatrix
  refine Matrix.mulVec_injective_of_isUnit hu ?_
  rw [Matrix.mulVec_zero]
  funext i
  have := h (Pi.single i 1)
  rw [hA_eq, show (fun j => cA D ((Pi.single i 1 : Fin B.rank → AE D) j)) = Pi.single i 1 from
    funext fun j => by by_cases e : j = i <;> simp [e], single_one_dotProduct] at this
  exact this

theorem suppAt_iff {ε : AE D} {g : GA D B} : SuppAt ε B g ↔ (ε + cA D ε) • (mt B g - 1) = mt B g - 1 :=
  ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

theorem suppAt_iff_vec {ε : AE D} {g : GA D B} :
    SuppAt ε B g ↔ ∀ x, (ε + cA D ε) • ((mt B g).mulVec x - x) = (mt B g).mulVec x - x := by
  rw [suppAt_iff]
  refine ⟨fun h x => ?_, fun h => Matrix.mulVec_injective (funext fun x => ?_)⟩
  · simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using congrArg (· *ᵥ x) h
  · simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using h x

theorem suppAt_one (ε : AE D) : SuppAt ε B 1 := by
  rw [suppAt_iff, mt_one, sub_self, smul_zero]

theorem suppAt_mul {ε : AE D} {g h : GA D B} (hg : SuppAt ε B g) (hh : SuppAt ε B h) : SuppAt ε B (g * h) := by
  have e : mt B (g * h) - 1 = (mt B g - 1) * mt B h + (mt B h - 1) := by
    rw [mt_mul, Matrix.sub_mul, Matrix.one_mul, sub_add_sub_cancel]
  rw [suppAt_iff, e, smul_add, ← Matrix.smul_mul, suppAt_iff.1 hg, suppAt_iff.1 hh]

theorem suppAt_inv {ε : AE D} {g : GA D B} (hg : SuppAt ε B g) : SuppAt ε B g⁻¹ := by
  have h := suppAt_iff.1 hg
  have h1 : mt B g⁻¹ - 1 = (mt B g - 1) * (-mt B g⁻¹) := by
    rw [Matrix.mul_neg, Matrix.sub_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul, neg_sub]
  rw [suppAt_iff, h1, ← Matrix.smul_mul, h]

def suppGrp (ε : AE D) (B : HSp D) : Subgroup (GA D B) where
  carrier := {g | SuppAt ε B g}
  one_mem' := suppAt_one ε
  mul_mem' := suppAt_mul
  inv_mem' := suppAt_inv

theorem suppAt_of_mem_Ex {d : BesselDatum A B ι} {ε : AE D} {i} {g : GA D B} (hg : g ∈ d.Ex ε i) : SuppAt ε B g :=
  (Subgroup.closure_le (suppGrp ε B)).2 (fun _ h => h.1) hg

theorem suppAt_of_mem_ExGe {d : BesselDatum A B ι} {ε : AE D} {p} {g : GA D B} (hg : g ∈ ExGe d ε p) :
    SuppAt ε B g :=
  (Subgroup.closure_le (suppGrp ε B)).2
    (Set.iUnion_subset fun _ => Set.iUnion_subset fun _ _ h => h.1) hg

theorem Ex_le_ExGe (d : BesselDatum A B ι) (ε : AE D) {p : ℕ} {i : Fin (d.ρ + 1)} (h : p ≤ i.1) :
    d.Ex ε i ≤ ExGe d ε p :=
  Subgroup.closure_mono fun _ hg => Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨h, hg⟩⟩

theorem mem_GfC {e : AE D} (he : IsSplitIdem D e) {g : GA D B} (hg : SuppAt e B g) : g ∈ GfC B := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt B g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt B g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

theorem commute_of_apart {ε ε' : AE D} (h : (ε + cA D ε) * (ε' + cA D ε') = 0) {g g' : GA D B}
    (hg : SuppAt ε B g) (hg' : SuppAt ε' B g') : g * g' = g' * g := by
  have h1 : (mt B g - 1) * (mt B g' - 1) = 0 := by
    rw [← suppAt_iff.1 hg, ← suppAt_iff.1 hg', Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, zero_smul]
  have h2 : (mt B g' - 1) * (mt B g - 1) = 0 := by
    rw [← suppAt_iff.1 hg, ← suppAt_iff.1 hg', Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm, h, zero_smul]
  refine mt_inj ?_
  rw [mt_mul, mt_mul]
  have : mt B g * mt B g' - mt B g' * mt B g = (mt B g - 1) * (mt B g' - 1) - (mt B g' - 1) * (mt B g - 1) := by
    noncomm_ring
  rw [h1, h2, sub_zero, sub_eq_zero] at this
  exact this

theorem hA_iA (hι : HSpace.IsIsomEmb A B ι) (s t : Fin A.rank → AE D) : hA B (iA ι s) (iA ι t) = hA A s t := by
  have e : ∀ s, iA ι s = ∑ l, s l • vecA B (ι (A.frame l)) := fun s => by
    rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]
  have e2 : ∀ l, hA B (vecA B (ι (A.frame l))) (iA ι t) = ∑ k, cA D (t k) * incA D (A.gram k l) := fun l => by
    rw [← hA_herm, e, GlobalTheory.BesselCompare.hA_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA_smul, RingHom.map_mul, hA_herm, hA_vec]
    congr 2
    exact hι _ _
  rw [e s, GlobalTheory.BesselCompare.hA_sum]
  simp only [hA_smul, e2]
  rw [hA, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem hA_vec_iA {v : B.V} (h : ∀ x, B.hD v (ι x) = 0) (t : Fin A.rank → AE D) : hA B (vecA B v) (iA ι t) = 0 := by
  rw [← hA_herm, iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec, GlobalTheory.BesselCompare.hA_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hA_smul, RingHom.map_mul, hA_herm, hA_vec, h, map_zero, mul_zero]

theorem iA_smul (a : AE D) (t : Fin A.rank → AE D) : iA ι (a • t) = a • iA ι t := Matrix.mulVec_smul _ _ _

theorem iA_add (s t : Fin A.rank → AE D) : iA ι (s + t) = iA ι s + iA ι t := Matrix.mulVec_add _ _ _

theorem iA_neg (t : Fin A.rank → AE D) : iA ι (-t) = -iA ι t := Matrix.mulVec_neg _ _

theorem besselDatum_auxiliaryVector_orthogonal_image (d : BesselDatum A B ι) (i) (x : A.V) : B.hD (d.aux i) (ι x) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; exact d.zA x
  · rw [Fin.snoc_castSucc]; exact d.eA j x

theorem dual_perp (d : BesselDatum A B ι) (i) (x : A.V) : B.hD (dual d i) (ι x) = 0 := by
  unfold dual
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    have := d.zA x
    unfold HSpace.hD at this ⊢
    rw [map_smul, this, smul_zero]
  · rw [Fin.snoc_castSucc]; exact d.fA j x

end GlobalTheory.RootExch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardKilledByInType
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertDivUniq

def minSum (s : List ℕ) (k : ℕ) : ℕ := (s.map (fun a => min a k)).sum

theorem minSum_succ (s : List ℕ) (k : ℕ) :
    minSum s (k + 1) = minSum s k + s.countP (fun a => k < a) := by
  induction s with
  | nil => simp [minSum]
  | cons a s ih =>
    simp only [minSum, List.map_cons, List.sum_cons, List.countP_cons] at ih ⊢
    rw [ih]
    by_cases h : k < a
    · simp [h]; omega
    · simp [h]; omega

theorem countP_lt_eq (s : List ℕ) (k : ℕ) :
    s.countP (fun a => k < a) = s.count (k + 1) + s.countP (fun a => k + 1 < a) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.countP_cons, List.count_cons]
    rw [ih]
    by_cases h1 : k < a <;> by_cases h2 : a = k + 1 <;> by_cases h3 : k + 1 < a <;> simp [h1, h2, h3] <;> omega

theorem eq_of_minSum {s t : List ℕ} (hs : s.Pairwise (· ≥ ·)) (hs0 : ∀ a ∈ s, 0 < a)
    (ht : t.Pairwise (· ≥ ·)) (ht0 : ∀ a ∈ t, 0 < a) (h : ∀ k, minSum s k = minSum t k) : s = t := by
  have hc : ∀ k, s.countP (fun a => k < a) = t.countP (fun a => k < a) := fun k => by
    have := minSum_succ s k; have := minSum_succ t k; have := h k; have := h (k + 1); omega
  have hcount : ∀ a, s.count a = t.count a := by
    intro a
    rcases a with _ | a
    · rw [List.count_eq_zero.2 (fun h0 => lt_irrefl 0 (hs0 0 h0)),
        List.count_eq_zero.2 (fun h0 => lt_irrefl 0 (ht0 0 h0))]
    · have := countP_lt_eq s a; have := countP_lt_eq t a; have := hc a; have := hc (a + 1); omega
  exact List.Perm.eq_of_pairwise' hs ht (List.perm_iff_count.2 hcount)

theorem sum_map_eq (s : List ℕ) (f : ℕ → ℕ) : (s.map f).sum = ∑ i : Fin s.length, f (s.get i) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (n := s.length) (fun i => f ((a :: s).get i))).symm

variable {E : Type} [Field E] [NumberField E]

def killedBy {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (I : Ideal (𝓞 E)) : Set M := {x | ∀ r ∈ I, r • x = 0}

theorem card_killedBy_congr {M N : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup N] [Module (𝓞 E) N]
    (e : M ≃ₗ[𝓞 E] N) (I : Ideal (𝓞 E)) :
    Nat.card (killedBy I : Set M) = Nat.card (killedBy I : Set N) :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    simp only [killedBy, Set.mem_setOf_eq]
    refine forall₂_congr fun r _ => ?_
    rw [LinearEquiv.coe_toEquiv, ← map_smul, LinearEquiv.map_eq_zero_iff])

theorem card_killedBy_inType (Q : Ideal (𝓞 E)) (s : List ℕ) (I : Ideal (𝓞 E)) :
    Nat.card (killedBy I : Set (Formalism.L2.Col.inType Q s)) =
      ∏ i : Fin s.length, Nat.card (killedBy I : Set (𝓞 E ⧸ Q ^ s.get i)) := by
  rw [← Nat.card_pi]
  refine Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans Equiv.subtypePiEquivPi)
  simp only [killedBy, Set.mem_setOf_eq]
  constructor
  · intro h i r hr; exact congrFun (h r hr) i
  · intro h r hr; funext i; exact h i r hr

theorem card_quot_pow (Q : Ideal (𝓞 E)) (n : ℕ) : Nat.card (𝓞 E ⧸ Q ^ n) = Ideal.absNorm Q ^ n := by
  rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem mem_killedBy_iff (Q : Ideal (𝓞 E)) (hQ0 : Q ≠ ⊥) (a k : ℕ) (x : 𝓞 E) :
    (∀ r ∈ Q ^ k, r * x ∈ Q ^ a) ↔ x ∈ Q ^ (a - k) := by
  constructor
  · intro H
    rcases le_or_gt a k with hak | hak
    · rw [Nat.sub_eq_zero_of_le hak, pow_zero, Ideal.one_eq_top]; trivial
    · have hle : Q ^ k * Ideal.span {x} ≤ Q ^ a := Ideal.mul_le.2 fun r hr y hy => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
        rw [mul_left_comm]; exact Ideal.mul_mem_left _ c (H r hr)
      have hd := Ideal.dvd_iff_le.2 hle
      rw [show Q ^ a = Q ^ k * Q ^ (a - k) by rw [← pow_add]; congr 1; omega] at hd
      have hQ : Q ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
      have := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left (pow_ne_zero k hQ)).1 hd)
      exact (Ideal.span_singleton_le_iff_mem _).1 this
  · intro hx r hr
    have := Ideal.mul_mem_mul hr hx
    rw [← pow_add] at this
    exact Ideal.pow_le_pow_right (by omega) this

theorem card_killedBy_quot (Q : Ideal (𝓞 E)) (hQ0 : Q ≠ ⊥) (a k : ℕ) :
    Nat.card (killedBy (Q ^ k) : Set (𝓞 E ⧸ Q ^ a)) = Ideal.absNorm Q ^ min a k := by
  have hle : Q ^ a ≤ Q ^ (a - k) := Ideal.pow_le_pow_right (Nat.sub_le a k)
  have hset : (killedBy (Q ^ k) : Set (𝓞 E ⧸ Q ^ a)) =
      (((Q ^ (a - k)).map (Ideal.Quotient.mk (Q ^ a)) : Ideal (𝓞 E ⧸ Q ^ a)) : Set (𝓞 E ⧸ Q ^ a)) := by
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [killedBy, Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_quotient_iff_mem hle]
    rw [← mem_killedBy_iff Q hQ0 a k x]
    refine forall₂_congr fun r _ => ?_
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  rw [hset]
  have h1 := Submodule.card_eq_card_quotient_mul_card ((Q ^ (a - k)).map (Ideal.Quotient.mk (Q ^ a)))
  rw [Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv, card_quot_pow, card_quot_pow] at h1
  have hq : 0 < Ideal.absNorm Q := Nat.pos_of_ne_zero (fun h0 => hQ0 (Ideal.absNorm_eq_zero_iff.1 h0))
  have ha : Ideal.absNorm Q ^ a = Ideal.absNorm Q ^ min a k * Ideal.absNorm Q ^ (a - k) := by
    rw [← pow_add]; congr 1; omega
  rw [ha] at h1
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos hq _) h1).symm

theorem inType_exps_unique : ∀ {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (s t : List ℕ),
    s.Pairwise (· ≥ ·) → (∀ a ∈ s, 0 < a) → t.Pairwise (· ≥ ·) → (∀ a ∈ t, 0 < a) →
    Nonempty (inType Q.asIdeal s ≃ₗ[𝓞 E] inType Q.asIdeal t) → s = t := by
  intro E _ _ Q s t hs hs0 ht ht0 ⟨e⟩
  refine eq_of_minSum hs hs0 ht ht0 fun k => ?_
  have hq : 2 ≤ Ideal.absNorm Q.asIdeal := by
    have h0 : Ideal.absNorm Q.asIdeal ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h1 => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
    omega
  have key : ∀ u : List ℕ, Nat.card (killedBy (Q.asIdeal ^ k) : Set (inType Q.asIdeal u)) =
      Ideal.absNorm Q.asIdeal ^ minSum u k := fun u => by
    rw [card_killedBy_inType, minSum, sum_map_eq, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => card_killedBy_quot Q.asIdeal Q.ne_bot _ k
  have := card_killedBy_congr e (Q.asIdeal ^ k)
  rw [key, key] at this
  exact Nat.pow_right_injective hq this

end GlobalTheory.InertDivUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartanExchangeUnimodularInertPrimeStatement
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_exchange_unimodular_inert_prime : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (n : ℕ), CartanInert E n := by
  first | exact @GlobalTheory.CartanInertPf.cartanInert | exact GlobalTheory.CartanInertPf.cartanInert | (intros; apply GlobalTheory.CartanInertPf.cartanInert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
section
open Formalism.BasicNotions

namespace GlobalTheory.VecTheta

theorem vecThetaSD : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := fun _ =>
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_stepVec h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_thPVec h⟩

end GlobalTheory.VecTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DownwardLevelMoveReachesKernelLatticeStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downwardLevelMove_reaches_kernelLattice : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (γ : GL (Fin (D.R.N i)) D.host.E), loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (clsCrd D u i hi c) → (∀ (x : ↥(Ld D u i hi c')) (hx : γ.1 *ᵥ x.1 ∈ Lk A i hi v c), (D.fm u).fv i v c' (P.pr v c' x) = g (P.prk v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).L = loc (A.res v) (Lk A i hi v c) ∧ ∀ x ∈ loc (A.res v) (Lk A i hi v c), ((pc P v c').act (glE γ)).f x = g (locExt (A.res v) (Lk A i hi v c) (P.prk v c) x) := by
  first | exact @GlobalTheory.LevelHecke.pc_act_down | exact GlobalTheory.LevelHecke.pc_act_down | (intros; apply GlobalTheory.LevelHecke.pc_act_down <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLocalDensityStandardLatticeBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_localDensity_standardLattice_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F), 1 ≤ M → IsHermND σ J → β ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ m, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F (Fv F v) β) m → |(m (latV b v)).toReal - 1| * (Ideal.absNorm v.asIdeal : ℝ) ^ M ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  first | exact @GlobalTheory.GaugeDensity.local_density_bound | exact GlobalTheory.GaugeDensity.local_density_bound | (intros; apply GlobalTheory.GaugeDensity.local_density_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInvariantHaarFamilyAdelicUnitaryStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basisInvariant_haar_family_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ G : GaugeFam F E σ, G.IsHaar ∧ G.BasisInv := by
  first | exact @GlobalTheory.GaugeRef.exists_isHaar_basisInv | exact GlobalTheory.GaugeRef.exists_isHaar_basisInv | (intros; apply GlobalTheory.GaugeRef.exists_isHaar_basisInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomiaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bilinearFischerPairing_matrixEntryPolynomialRing : ∀ (ι : Type) [Fintype ι] (m n : ℕ), ∃ B : Pol ι m n →ₗ[ℂ] Pol ι m n →ₗ[ℂ] ℂ, (∀ Q, (∀ P, B P Q = 0) → Q = 0) ∧ (∀ a b P Q, B (subst a b P) Q = B P (subst (fun τ => (a τ).transpose) (fun τ => (b τ).transpose) Q)) ∧ ∀ (ℓ : Pol ι m n →ₗ[ℂ] ℂ) (d : ℕ), (∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → ℓ (MvPolynomial.monomial α 1) = 0) → ∃ Q, ∀ P, B P Q = ℓ P := by
  first | exact @GlobalTheory.DefLift.BilFischer.exists_pair | exact GlobalTheory.DefLift.BilFischer.exists_pair | (intros; apply GlobalTheory.DefLift.BilFischer.exists_pair <;> assumption)
end

