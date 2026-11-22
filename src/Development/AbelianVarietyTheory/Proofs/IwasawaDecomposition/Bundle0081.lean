import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdRStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR : ∀ (l : ℕ) [Fact l.Prime], ∀ (e : Per.Fl l) (t : Per.Acris l), e.untilt = 1 → IsLogA e t → (∀ t' : Per.Acris l, IsLogA e t' → t' = t) ∧ (∀ g : Per.Gq l, IsLogA (Per.σF g e) (sigA g t)) ∧ IsLogA (e ^ l) (phiA l t) ∧ ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Per.IsLog l e (j t) := by
  first | exact @GlobalTheory.MemLoc.LogFun.log_fun | exact GlobalTheory.MemLoc.LogFun.log_fun | (intros; apply GlobalTheory.MemLoc.LogFun.log_fun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfQuotFontaineXiPowTorsionFreeSeparated
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem quot_pow_torsionFree_sep {A O : Type*} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O]
    (θ : A →+* O) (ξ p : A) (hξ : ξ ≠ 0) (hker : ∀ a, θ a = 0 ↔ ξ ∣ a) (hp : θ p ≠ 0)
    (hsep : ∀ x : O, (∀ k : ℕ, θ p ^ k ∣ x) → x = 0) (n : ℕ) :
    (∀ a : A, ξ ^ n ∣ p * a → ξ ^ n ∣ a) ∧
      ∀ a : A, (∀ k : ℕ, ∃ b : A, ξ ^ n ∣ a - p ^ k * b) → ξ ^ n ∣ a := by
  have h0 : ∀ (m : ℕ) (x : A), ξ ^ (m + 1) ∣ x → θ x = 0 := fun m x hx =>
    (hker x).2 ((dvd_pow_self ξ m.succ_ne_zero).trans hx)
  have hθξ : θ ξ = 0 := (hker ξ).2 dvd_rfl
  induction n with
  | zero => simp
  | succ n ih =>
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have h1 := h0 n _ ha
      rw [map_mul] at h1
      obtain ⟨a', rfl⟩ := (hker a).1 ((mul_eq_zero.1 h1).resolve_left hp)
      rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left hξ] at ha
      rw [pow_succ', mul_dvd_mul_iff_left hξ]
      exact ih.1 a' ha
    · have h1 : θ a = 0 := hsep _ fun k => by
        obtain ⟨b, hb⟩ := ha k
        have h2 := h0 n _ hb
        rw [map_sub, map_mul, map_pow, sub_eq_zero] at h2
        exact ⟨θ b, h2⟩
      obtain ⟨a', rfl⟩ := (hker a).1 h1
      rw [pow_succ', mul_dvd_mul_iff_left hξ]
      refine ih.2 a' fun k => ?_
      obtain ⟨b, hb⟩ := ha k
      have h2 := h0 n _ hb
      rw [map_sub, h1, map_mul, map_pow, zero_sub, neg_eq_zero] at h2
      obtain ⟨b', rfl⟩ := (hker b).1 ((mul_eq_zero.1 h2).resolve_left (pow_ne_zero k hp))
      refine ⟨b', ?_⟩
      rwa [pow_succ', mul_left_comm, ← mul_sub, mul_dvd_mul_iff_left hξ] at hb

theorem ainf_quot_xi_pow_torsionFree_sep : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ ((l : ℕ) : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ ∀ a : Per.Ainf l, (∀ k : ℕ, ∃ b : Per.Ainf l, xi e ^ n ∣ a - ((l : ℕ) : Per.Ainf l) ^ k * b) → xi e ^ n ∣ a := by
  intro l _ e he n
  obtain ⟨-, hdom, -, hk⟩ := theta_ker_facts l
  obtain ⟨h1, h2⟩ := hk e he
  refine quot_pow_torsionFree_sep (Per.θ l) (xi e) _ h2 (fun a => ?_) ?_ (fun x hx => ?_) n
  · rw [← RingHom.mem_ker, h1, Ideal.mem_span_singleton]
  · rw [map_natCast]
    exact fun h => GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h)
  · rw [map_natCast] at hx
    refine IsHausdorff.haus (I := Ideal.span {((l : ℕ) : Per.OC l)}) inferInstance x fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx k

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLawsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdR_filtration_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ a : ℤ, Per.FilD l (a + 1) ≤ Per.FilD l a) ∧ (1 : Per.BdR l) ∈ Per.FilD l 0 ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ x : Per.BdR l, ∃ a, x ∈ Per.FilD l a) ∧ (∀ x : Per.BdR l, (∀ a, x ∈ Per.FilD l a) → x = 0) ∧ (∀ (g : Per.Gq l) (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a → Per.σD g x ∈ Per.FilD l a) ∧ ∀ (n : ℕ) (y : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
  first | exact @GlobalTheory.MemLoc.filD_laws | exact GlobalTheory.MemLoc.filD_laws | (intros; apply GlobalTheory.MemLoc.filD_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChangeAt
section
noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

def bcF (φ : K →+* K') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0') (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K')
    (f : B.S.Forms) : B'.S.Forms :=
  B'.S.basis.equivFun.symm (C *ᵥ fun k => φ (B.S.basis.equivFun f k))

structure BlockBaseChangeAt (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (ℓ : Lvl K G) (ℓ' : Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K') : Prop where

  bij : Function.Bijective C.mulVec

  H : Cᴴ * B'.S.H * C = B.S.H.map φ

  act : ∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ

  nab : B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)))

  sub : B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K)))

  X : ∀ χ' : G' → K', χ' ∈ ℓ'.X ↔ ∃ χ ∈ ℓ.X, χ' = fun g => φ (χ (e.symm g))

  P : ℓ'.P = ℓ.P.map e.toMonoidHom

  ψ : ∀ h : ℓ.P, ((ℓ'.ψ ⟨e h, P ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : K'ˣ) : K') = φ (ℓ.ψ h : K)

section Cx

open Formalism.IndefR.Cx Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}

theorem tC_cpt (cr : Crd A fc) (b : Bool) (j : Bs.J) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.tC cr b j t (cpt Bs.v0.embedding x) = X.θ' j t (X.jL j t (cr.toL X.zs b j t x)) := by
  have hx : x = ∑ k, x k • Pi.single k 1 := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, map_smulₛₗ, CxData.tC, lin, Fintype.linearCombination_apply, cpt]

end Cx

end GlobalTheory.Mem.R3.LiftLatBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockTriangularBlockIndexOfIffColBlockUTTwoBlock
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise {n r t : ℕ} (hn : n = r + t) (a : Fin n) :
    Formalism.L2.DIV.blkOf r t a = Formalism.L2.Col.coarse r [t] a.val ∧
      Formalism.L2.DIV.blk2 r a = Formalism.L2.Col.coarse r [t] a.val := by
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h]
  · have h' : r ≤ a.val := Nat.not_lt.mp h
    rw [Formalism.L2.Col.coarse_of_le h']
    have hlt : a.val - r < t := by omega
    have hd : (a.val - r) / t = 0 := Nat.div_eq_of_lt hlt
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h, hd, Formalism.L2.Col.blkIdx, hlt]

theorem blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks :
    ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ g : GL (Fin n) κ,
      (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) ∧
        (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) := by
  intro κ _ n r t hn g
  rw [Formalism.L2.DIV.mem_blockTri, Formalism.L2.DIV.mem_blockTri, Formalism.L2.Col.mem_btG]
  refine ⟨?_, ?_⟩
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).1]
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionLabelOfLabelMapLabel
section
open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

open Formalism.IrreducibleCountingLemmas.TYPES

theorem hasLabel_of_hasLabelO : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x)) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f := by
  intro g _ L C O h1 h2 h3 r τ f hτ hL
  obtain ⟨s, b, lam, hb, hl, hcon, rfl⟩ := hL
  have hc : ∀ c, 1 ≤ Fintype.card {i // b i = c} := fun c => by
    obtain ⟨i, hi⟩ := hb c
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  let Q : List ((ZMod g)[X] × GlobalTheory.GLq.Pc g) := (List.finRange s).map fun c =>
    (labO O (lam c), ⟨Fintype.card {i // b i = c},
      fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩)
  have hQ : Q.map Prod.snd = canonList b lam := by
    simp only [Q, canonList, List.map_map]
    rfl
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Q, List.mem_map] at hp
    obtain ⟨c, -, rfl⟩ := hp
    exact h1 _ _ (hc c) (Formalism.L2.PT.simple_transp _ (hl c).1) (Formalism.L2.PT.isCuspidal_transp _ (hl c).2)
  · rw [hQ]
    unfold GlobalTheory.GLq.degL canonList
    rw [List.map_map]
    have e : ((List.finRange s).map ((fun p : GlobalTheory.GLq.Pc g => p.1) ∘ fun c : Fin s =>
        (⟨Fintype.card {i // b i = c},
          fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ : GlobalTheory.GLq.Pc g))).sum =
        ∑ c : Fin s, Fintype.card {i // b i = c} := by
      rw [Fin.sum_univ_def]
      rfl
    rw [e, ← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv b), Fintype.card_fin]
  · simp only [Q, List.map_map]
    rw [Fin.prod_univ_def]
    rfl
  · rw [hQ]
    have ht : (fun x => LinearMap.trace ℂ (hcSpace (ZMod g) b lam) (hcRep (ZMod g) b lam x)) =
        GlobalTheory.GLq.hcL (canonList b lam) r := funext (h2 r s b lam hb)
    have := (h3 r s b lam τ hτ).1 hcon
    rw [ht] at this
    exact this

end GlobalTheory.SerCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBcrisToBdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem IsCrisP.on_ainf {l : ℕ} [Fact l.Prime] {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j)
    (a : Per.Ainf l) :
    j (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  rw [GlobalTheory.RingIface.tower]
  exact hj.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) a)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBlocksOfCuspidalCharacterList
section
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.SerCmp.ListBlocks

open Formalism.IrreducibleCountingLemmas.TYPES

theorem glEquiv_transp_cancel {g : ℕ} [Fact g.Prime] {F : Type} [Fintype F] [DecidableEq F] {n : ℕ}
    (E : F ≃ Fin n) (x : GL (Fin n) (ZMod g)) :
    (glEquiv (ZMod g) E.symm).symm ((glEquiv (ZMod g) E).symm x) = x := by
  ext i j
  rw [Formalism.L2.PT.coe_glEquiv_symm, Formalism.L2.PT.coe_glEquiv_symm]
  simp

theorem entry_eq {g : ℕ} [Fact g.Prime] {F : Type} [Fintype F] [DecidableEq F] {d : ℕ}
    (h : Fintype.card F = d) (V : FDRep ℂ (GL (Fin d) (ZMod g))) :
    (⟨Fintype.card F, fun x => (transp (Fintype.equivFin F)
      (transp ((finCongr h.symm).trans (Fintype.equivFin F).symm) V)).character x⟩ : GlobalTheory.GLq.Pc g) =
      ⟨d, fun x => V.character x⟩ := by
  generalize Fintype.equivFin F = E
  subst h
  refine Sigma.ext rfl (heq_of_eq (funext fun x => ?_))
  dsimp only
  rw [Formalism.L2.PT.character_transp, Formalism.L2.PT.character_transp]
  congr 1
  have : (finCongr (rfl : Fintype.card F = Fintype.card F)).trans E.symm = E.symm := by ext; simp
  rw [this, glEquiv_transp_cancel]

theorem exists_blocks (s : ℕ) (d : Fin s → ℕ) (r : ℕ) (hr : ∑ c, d c = r) :
    ∃ b : Fin r → Fin s, ∀ c, Fintype.card {i // b i = c} = d c := by
  subst hr
  refine ⟨fun i => (finSigmaFinEquiv.symm i).1, fun c => ?_⟩
  rw [Fintype.card_congr ((finSigmaFinEquiv.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype c))]
  simp

end GlobalTheory.SerCmp.ListBlocks

open Formalism.IrreducibleCountingLemmas.TYPES in
theorem GlobalTheory.SerCmp.canonList_of_cuspidal_list : ∀ (g : ℕ) [Fact g.Prime] (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q := by
  intro g _ Q hQ
  have H : ∀ c : Fin Q.length, ∃ V : FDRep ℂ (GL (Fin (Q.get c).1) (ZMod g)), 1 ≤ (Q.get c).1 ∧
      CategoryTheory.Simple V ∧ IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = (Q.get c).2 x := by
    intro c
    obtain ⟨h1, V, h2⟩ := hQ _ (List.get_mem Q c)
    exact ⟨V, h1, h2⟩
  choose V hd hVs hVc hVch using H
  have hsum : ∑ c : Fin Q.length, (Q.get c).1 = GlobalTheory.GLq.degL Q := by
    rw [GlobalTheory.GLq.degL]
    rw [← Fin.sum_univ_getElem]
    exact Fintype.sum_equiv (finCongr (List.length_map _).symm) _ _ (fun c => by simp)
  obtain ⟨b, hcard⟩ := GlobalTheory.SerCmp.ListBlocks.exists_blocks Q.length (fun c => (Q.get c).1) _ hsum
  refine ⟨b, fun c => transp ((finCongr (hcard c).symm).trans (Fintype.equivFin _).symm) (V c), ?_, ?_, ?_⟩
  · intro c
    have : 0 < Fintype.card {i // b i = c} := by rw [hcard c]; exact hd c
    obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.1 this
    exact ⟨i, hi⟩
  · intro c
    exact ⟨Formalism.L2.PT.simple_transp _ (hVs c), Formalism.L2.PT.isCuspidal_transp _ (hVc c)⟩
  · apply List.ext_get (GlobalTheory.SerCmp.canonList_length _ _)
    intro n h1 h2
    simp only [GlobalTheory.SerCmp.canonList, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    rw [GlobalTheory.SerCmp.ListBlocks.entry_eq (hcard _) (V _)]
    have key : ∀ c, (⟨(Q.get c).1, fun x => (V c).character x⟩ : GlobalTheory.GLq.Pc g) = Q.get c := fun c =>
      Sigma.ext rfl (heq_of_eq (_root_.funext fun x => hVch c x))
    rw [key]
    simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdRStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_bcris_to_bdR : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → ∃ ι : Per.Bcris l →+* Per.BdR l, (∀ x : Per.Acris l, ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x)) ∧ Function.Injective ι := by
  first | exact @GlobalTheory.MemLoc.exists_iota_cris_dR | exact GlobalTheory.MemLoc.exists_iota_cris_dR | (intros; apply GlobalTheory.MemLoc.exists_iota_cris_dR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAdicCompletionLocalizationProd
section
open IsLocalRing TensorProduct

namespace GlobalTheory.CompletionFactor

theorem exists_ringEquiv_prod_of_isIdempotentElem {S : Type*} [CommRing S] {e : S}
    (he : IsIdempotentElem e) :
    ∃ ε : S ≃+* (S ⧸ Ideal.span {1 - e}) × (S ⧸ Ideal.span {e}),
      ∀ x, (ε x).1 = Ideal.Quotient.mk _ x := by
  have hc : IsCoprime (Ideal.span {1 - e}) (Ideal.span {e} : Ideal S) := by
    rw [Ideal.isCoprime_span_singleton_iff]
    exact ⟨1, 1, by ring⟩
  have hb : (⊥ : Ideal S) = Ideal.span {1 - e} ⊓ Ideal.span {e} := by
    rw [Ideal.inf_eq_mul_of_isCoprime hc, Ideal.span_singleton_mul_span_singleton, sub_mul,
      one_mul, he.eq, sub_self, Ideal.span_singleton_zero]
  refine ⟨(RingEquiv.quotientBot S).symm.trans ((Ideal.quotEquivOfEq hb).trans
    (Ideal.quotientInfEquivQuotientProd _ _ hc)), fun x => ?_⟩
  rfl

theorem exists_local_factor {B S D : Type*} [CommRing B] [HenselianLocalRing B] [CommRing S]
    [Algebra B S] [Module.Finite B S] [CommRing D] [IsLocalRing D] (φ : S →+* D)
    (hφ : maximalIdeal B ≤ (maximalIdeal D).comap (φ.comp (algebraMap B S))) :
    ∃ e : S, IsIdempotentElem e ∧ IsLocalRing (S ⧸ Ideal.span {1 - e}) ∧
      ∃ ψ : (S ⧸ Ideal.span {1 - e}) →+* D, IsLocalHom ψ ∧
        ∀ x, ψ (Ideal.Quotient.mk _ x) = φ x := by
  have hq : ((maximalIdeal D).comap φ).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := B)
    rw [Ideal.comap_comap, ← (maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hφ]
    infer_instance
  obtain ⟨e, he, H⟩ := exists_idempotent_notMem_iff_of_henselian B ((maximalIdeal D).comap φ)
  have hl := isLocalRing_quotient_one_sub he _ H
  have h1 : φ e = 1 := by
    refine (IsIdempotentElem.iff_eq_one_of_isUnit ?_).1 (he.map φ)
    have := (H _ hq).2 rfl
    rwa [Ideal.mem_comap, notMem_maximalIdeal] at this
  have h0 : ∀ a ∈ Ideal.span {1 - e}, φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [h1]
  refine ⟨e, he, hl, Ideal.Quotient.lift _ φ h0, ⟨fun r hr => ?_⟩, fun x => rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hm := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {1 - e}))
    Ideal.Quotient.mk_surjective (K := maximalIdeal _)
  have h : (maximalIdeal _).comap (Ideal.Quotient.mk (Ideal.span {1 - e})) =
      (maximalIdeal D).comap φ := by
    rw [← H _ hm, ← one_sub_mem_iff_notMem_of_isIdempotentElem he, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
    exact zero_mem _
  rw [← notMem_maximalIdeal, ← Ideal.mem_comap, h, Ideal.mem_comap, notMem_maximalIdeal]
  exact hr

theorem bijective_of_complete_quotient {T C A R : Type*} [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] [CommRing C] [Algebra T C] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫]
    (h𝔫 : 𝔫.comap (algebraMap T C) = maximalIdeal T)
    [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (π : (AdicCompletion (maximalIdeal T) T ⊗[T] C) →+* R) (hπ : Function.Surjective π)
    (ψ : R →+* AdicCompletion (maximalIdeal A) A) [IsLocalHom ψ]
    (hψ : ∀ c : C, ψ (π (1 ⊗ₜ[T] c)) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c)) :
    Function.Bijective ψ := by
  let β₀ : C →+* R := π.comp (Algebra.TensorProduct.includeRight (R := T)).toRingHom
  have hβ₀ : ∀ c, β₀ c = π (1 ⊗ₜ[T] c) := fun c => rfl
  have hu : ∀ s : 𝔫.primeCompl, IsUnit (β₀ s) := fun s => by
    refine IsUnit.of_map ψ _ ?_
    rw [hβ₀, hψ]
    exact (IsLocalization.map_units A s).map _
  let β : A →+* R := IsLocalization.lift hu
  have hβ : ∀ c, β (algebraMap C A c) = π (1 ⊗ₜ[T] c) := fun c => IsLocalization.lift_eq hu c
  have hψβ : ψ.comp β = algebraMap A (AdicCompletion (maximalIdeal A) A) := by
    refine IsLocalization.ringHom_ext 𝔫.primeCompl (RingHom.ext fun c => ?_)
    simp only [RingHom.comp_apply, hβ, hψ]
  have hβm : ∀ a ∈ maximalIdeal A, β a ∈ maximalIdeal R := fun a ha => by
    by_contra h
    rw [notMem_maximalIdeal] at h
    have h2 : IsUnit ((ψ.comp β) a) := h.map ψ
    rw [hψβ] at h2
    exact notMem_maximalIdeal.2 (IsUnit.of_map _ _ h2) ha
  obtain ⟨χ, hχ, -⟩ := exists_extend_adicCompletion β (maximalIdeal A) (maximalIdeal R) (k := 1)
    (by rw [pow_one, Ideal.map_le_iff_le_comap]; exact hβm)
  have h₁ : ψ.comp χ = RingHom.id _ := by
    refine adicCompletion_ringHom_ext (maximalIdeal A).fg_of_isNoetherianRing
      (maximalIdeal (AdicCompletion (maximalIdeal A) A)) (k := 1) ?_ ?_
    · rw [pow_one, RingHom.comp_assoc, hχ, hψβ, AdicCompletion.maximalIdeal_eq_map]
    · rw [RingHom.comp_assoc, hχ, hψβ, RingHom.id_comp]
  have hC : ∀ c : C, χ (ψ (π (1 ⊗ₜ[T] c))) = π (1 ⊗ₜ[T] c) := fun c => by
    rw [hψ, ← RingHom.comp_apply, hχ, hβ]
  have hT : ∀ t : T, (algebraMap T (AdicCompletion (maximalIdeal T) T) t) ⊗ₜ[T] (1 : C) =
      1 ⊗ₜ[T] algebraMap T C t := fun t => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]
  have hL : π.comp Algebra.TensorProduct.includeLeftRingHom =
      ((χ.comp ψ).comp π).comp Algebra.TensorProduct.includeLeftRingHom := by
    refine adicCompletion_ringHom_ext (maximalIdeal T).fg_of_isNoetherianRing
      (maximalIdeal R) (k := 1) ?_ ?_
    · rw [pow_one, Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply,
        Algebra.TensorProduct.includeLeftRingHom_apply, hT, ← hβ]
      apply hβm
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔫, ← Ideal.mem_comap, h𝔫]
      exact ht
    · refine RingHom.ext fun t => ?_
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, hT, hC]
  have h₂ : ∀ x, χ (ψ (π x)) = π x := by
    intro x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a c =>
      have e1 : a ⊗ₜ[T] c = (a ⊗ₜ[T] (1 : C)) * (1 ⊗ₜ[T] c) := by simp
      have e2 : π (a ⊗ₜ[T] (1 : C)) = χ (ψ (π (a ⊗ₜ[T] (1 : C)))) := congr($hL a)
      rw [e1, map_mul, map_mul, map_mul, ← e2, hC]
  refine Function.bijective_iff_has_inverse.2 ⟨χ, fun r => ?_, fun y => congr($h₁ y)⟩
  obtain ⟨x, rfl⟩ := hπ r
  exact h₂ x

theorem exists_ringEquiv_completion_prod : ∀ (T C A : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing C] [Algebra T C] [Module.Finite T C] [CommRing A] [IsLocalRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫], 𝔫.comap (algebraMap T C) = maximalIdeal T → ∃ (S' : Type) (_ : CommRing S') (e : (AdicCompletion (maximalIdeal T) T ⊗[T] C) ≃+* (AdicCompletion (maximalIdeal A) A × S')), ∀ c : C, (e ((1 : AdicCompletion (maximalIdeal T) T) ⊗ₜ[T] c)).1 = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := by
  intro T C A _ _ _ _ _ _ _ _ _ 𝔫 _ _ h𝔫
  have hCn : IsNoetherianRing C := IsNoetherianRing.of_finite T C
  have hAn : IsNoetherianRing A := IsLocalization.isNoetherianRing 𝔫.primeCompl A hCn
  have hTn := AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)
  let g : C →+* AdicCompletion (maximalIdeal A) A := (algebraMap A _).comp (algebraMap C A)
  have hg : maximalIdeal T ≤ (maximalIdeal _).comap (g.comp (algebraMap T C)) := by
    intro t ht
    rw [Ideal.mem_comap, AdicCompletion.maximalIdeal_eq_map]
    refine Ideal.mem_map_of_mem _ (?_ : algebraMap C A (algebraMap T C t) ∈ maximalIdeal A)
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔫, ← Ideal.mem_comap, h𝔫]
    exact ht
  obtain ⟨α, hα, -⟩ := exists_extend_adicCompletion (g.comp (algebraMap T C)) (maximalIdeal T)
    (maximalIdeal _) (k := 1) (by rw [pow_one, Ideal.map_le_iff_le_comap]; exact hg)
  obtain ⟨φ, hφa, hφc⟩ : ∃ φ : (AdicCompletion (maximalIdeal T) T ⊗[T] C) →+*
      AdicCompletion (maximalIdeal A) A,
      φ.comp (algebraMap (AdicCompletion (maximalIdeal T) T) _) = α ∧
        ∀ c, φ (1 ⊗ₜ[T] c) = g c := by
    letI : Algebra T (AdicCompletion (maximalIdeal A) A) := (g.comp (algebraMap T C)).toAlgebra
    let α' : AdicCompletion (maximalIdeal T) T →ₐ[T] AdicCompletion (maximalIdeal A) A :=
      { α with commutes' := fun t => congr($hα t) }
    let g' : C →ₐ[T] AdicCompletion (maximalIdeal A) A := { g with commutes' := fun t => rfl }
    refine ⟨(Algebra.TensorProduct.lift α' g' fun _ _ => .all _ _).toRingHom,
      RingHom.ext fun a => ?_, fun c => ?_⟩
    · change Algebra.TensorProduct.lift α' g' (fun _ _ => .all _ _) (a ⊗ₜ[T] 1) = α' a
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    · change Algebra.TensorProduct.lift α' g' (fun _ _ => .all _ _) (1 ⊗ₜ[T] c) = g' c
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hH := henselianLocalRing_of_henselianRing (AdicCompletion (maximalIdeal T) T)
  obtain ⟨e, he, hl, ψ, hψl, hψ⟩ := exists_local_factor (B := AdicCompletion (maximalIdeal T) T) φ
    (by
      rw [hφa, AdicCompletion.maximalIdeal_eq_map (R := T), Ideal.map_le_iff_le_comap,
        Ideal.comap_comap, hα]
      exact hg)
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local
    (AdicCompletion (maximalIdeal T) T)
    ((AdicCompletion (maximalIdeal T) T ⊗[T] C) ⧸ Ideal.span {1 - e})
  have hψc : ∀ c : C, ψ (Ideal.Quotient.mk _ (1 ⊗ₜ[T] c)) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := fun c => by
    rw [hψ, hφc]; rfl
  have hb := bijective_of_complete_quotient 𝔫 h𝔫 _ Ideal.Quotient.mk_surjective ψ hψc
  obtain ⟨ε, hε⟩ := exists_ringEquiv_prod_of_isIdempotentElem he
  refine ⟨_, inferInstance, ε.trans ((RingEquiv.ofBijective ψ hb).prodCongr (RingEquiv.refl _)),
    fun c => ?_⟩
  rw [← hψc, ← hε]
  rfl

end GlobalTheory.CompletionFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueLineBundlesStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_glue_disjoint_cover : ∀ (X : Scheme.{0}) (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) → (∀ x, ∃ a, x ∈ V a) → ∀ (M : ∀ a, LB (V a).toScheme), (∀ a, (M a).IsLB) → ∃ N : LB X, N.IsLB ∧ ∀ a, LBIso (N.pull (V a).ι) (M a) := by
  first | exact @GlobalTheory.glue_lineBundles | exact GlobalTheory.glue_lineBundles | (intros; apply GlobalTheory.glue_lineBundles <;> assumption)
end

