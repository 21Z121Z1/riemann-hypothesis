import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0393
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvertibleMatrixLastLineGiven
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

private theorem det_updateRow_one' {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    (r : n) (b : n → R) : (updateRow (1 : Matrix n n R) r b).det = b r := by
  rw [← det_transpose, ← updateCol_transpose, transpose_one, ← cramer_apply, cramer_one]
  rfl

theorem exists_GL_lastRow_eq (k : Type) [Field k] (m : ℕ) (a : Fin (m + 1) → k) (ha : a ≠ 0) :
    ∃ g : GL (Fin (m + 1)) k, ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = a j := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hN : (updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m))).det ≠ 0 := by
    rw [det_updateRow_one']
    simpa using hi
  have hM : ((updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m))).submatrix id (Equiv.swap i (Fin.last m))).det ≠ 0 := by
    rw [det_permute']
    refine mul_ne_zero ?_ hN
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i (Fin.last m))) with h | h <;> simp [h]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hM, fun j => ?_⟩
  show updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m)) (Fin.last m) (Equiv.swap i (Fin.last m) j) = a j
  rw [updateRow_self, Function.comp_apply, Equiv.swap_apply_self]

end GlobalTheory.CompanionTheory.MirFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemKNInvMulMemInfMapConj
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_mem_KN_inv_mul_mem_inf_map_conj
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)) :
    IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) →
    HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∀ y ∈ J,
      ∃ a ∈ KN k N J d hd, a⁻¹ * y ∈
        J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  intro _ _ hfact _ t hdom y hy
  obtain ⟨-, hNl, hM⟩ := hdom
  obtain ⟨u, hu, b, hb, n, hn, hyf⟩ := hfact y⁻¹ (J.inv_mem hy)
  obtain ⟨huJ, -⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hbJ, x, rfl⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨hnJ, hnN⟩ := Subgroup.mem_inf.1 hn
  have hy' : y = n⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * u⁻¹ := by
    have : y = (y⁻¹)⁻¹ := (inv_inv y).symm
    rw [this, hyf]; group
  refine ⟨n⁻¹, (KN k N J d hd).inv_mem (Subgroup.mem_inf.2 ⟨hnJ, hnN⟩), ?_⟩
  have hred : (n⁻¹)⁻¹ * y = (leviEmb k (stdBlocks d hd) x)⁻¹ * u⁻¹ := by
    rw [hy']; group
  rw [hred]
  set g := leviEmb k (stdBlocks d hd) t with hg
  have hxKM : x⁻¹ ∈ KM k N J d hd :=
    (KM k N J d hd).inv_mem (show x ∈ (J).comap (leviEmb k (stdBlocks d hd)) from hbJ)
  have h1 : g⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * g ∈ J := by
    have h2 : t⁻¹ * x⁻¹ * t ∈ KM k N J d hd := (hM _ hxKM).2
    have h3 : leviEmb k (stdBlocks d hd) (t⁻¹ * x⁻¹ * t) ∈ J := h2
    simpa [hg, map_mul, map_inv] using h3
  have h4 : g⁻¹ * u⁻¹ * g ∈ J :=
    (Subgroup.mem_inf.1 (hNl _ ((KNl k N J d hd).inv_mem hu))).1
  refine Subgroup.mem_inf.2 ⟨J.mul_mem (J.inv_mem hbJ) (J.inv_mem huJ), ?_⟩
  refine Subgroup.mem_map.2 ⟨(g⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * g) * (g⁻¹ * u⁻¹ * g),
    J.mul_mem h1 h4, ?_⟩
  simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Whit

namespace GlobalTheory.CompanionTheory.AdmDict

theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) :
    GlobalTheory.PRep.fixed ρ K = GroundTheory.Automorphic.fixedVectors ρ K := by
  ext v
  constructor
  · intro hv h hh
    simpa using hv ⟨h, hh⟩
  · intro hv h
    simpa using hv h h.2

theorem isAdmissible_iff : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ := by
  intro G V _ _ _ _ _ ρ
  have hs : GlobalTheory.PRep.IsSmooth ρ ↔ GroundTheory.Automorphic.IsSmooth ρ := Iff.rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hs.1 h1, fun K hc ho => ?_⟩
    have := h2 K ho hc
    rwa [fixed_eq_fixedVectors] at this
  · rintro ⟨h1, h2⟩
    refine ⟨hs.2 h1, fun K ho hc => ?_⟩
    rw [fixed_eq_fixedVectors]
    exact h2 K hc ho

end GlobalTheory.CompanionTheory.AdmDict
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProjectiveOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_existence_projective_open : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {N : ℕ} {Y : Scheme.{0}} (i : Y ⟶ projectiveSpace A N), IsClosedImmersion i → ∀ (O : Y.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩; Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := by
  first | exact @GlobalTheory.CompanionTheory.GE.statement_open_projective | exact GlobalTheory.CompanionTheory.GE.statement_open_projective | (intros; apply GlobalTheory.CompanionTheory.GE.statement_open_projective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredientStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_kazhdan_contragredient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GKLocal k → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra | exact GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra | (intros; apply GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg

section Quot

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y]
  [Module ℂ Y]

end Quot

section Main

variable {k : Type} [Field k] [TopologicalSpace k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem isGeneric_of_surjective {τ : Representation ℂ (GL (Fin N) k) W} {π : Representation ℂ (GL (Fin N) k) V}
    (q : τ.IntertwiningMap π) (hq : Function.Surjective q) (h : IsGeneric π) : IsGeneric τ := by
  obtain ⟨ψ, h1, h2, h3⟩ := h
  refine ⟨ψ, h1, h2, nontrivial_twJacquet_of_surjective q.toLinearMap hq
    (fun u v => Submodule.subset_span ⟨u, q v, ?_⟩) h3⟩
  rw [map_sub, map_smul]
  exact congrArg (· - _) (q.isIntertwining _ _ _ v)

end Main

end GlobalTheory.CompanionTheory.BZSeg

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenFiniteStatement
section
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_eigen_finite : PositivityTheory.Rg.BcB.F.Tail.PExp.HkEFin := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin | exact GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin | (intros; apply GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFactsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bound_facts : PositivityTheory.RgBcC.LfSt.HbFacts := by
  first | exact @GlobalTheory.CompanionTheory.HbBasis.hbFacts | exact GlobalTheory.CompanionTheory.HbBasis.hbFacts | (intros; apply GlobalTheory.CompanionTheory.HbBasis.hbFacts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactors
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd.ProdDrop

section Blocks

variable (k : Type) [Field k] {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r)
  (ho : StrictMono o) (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (hd' : ∑ a, d (o a) = N)

include ho hz

theorem mem_parab_drop (g : GL (Fin N) k) :
    g ∈ parab k (stdBlocks d hd) ↔ g ∈ parab k (stdBlocks (fun a => d (o a)) hd') := by
  have hE := GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty d hd o ho hz hd'
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro h a b i j hab
    rw [hE, hE]
    exact h _ _ i j (ho hab)
  · intro h a b i j hab
    obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
    obtain ⟨b, rfl⟩ := hz b (Nat.pos_iff_ne_zero.1 (Fin.pos j))
    have := h a b i j (ho.lt_iff_lt.1 hab)
    rwa [hE, hE] at this

theorem dropHom_leviProj (p : parab k (stdBlocks d hd)) (q : parab k (stdBlocks (fun a => d (o a)) hd'))
    (h : (p : GL (Fin N) k) = q) :
    dropHom d o (leviProj k (stdBlocks d hd) p) = leviProj k (stdBlocks (fun a => d (o a)) hd') q := by
  have hE := GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty d hd o ho hz hd'
  funext a
  ext i j
  show (leviProj k (stdBlocks d hd) p (o a) : Matrix _ _ k) i j = _
  rw [leviProj_apply, leviProj_apply, hE, hE, h]

theorem modExp_drop (a : Fin r') :
    modExp (fun j => Fin (d j)) (o a) = modExp (fun b => Fin (d (o b))) a := by
  have h0 : ∀ j, j ∉ Set.range o → d j = 0 := fun j hj => by_contra fun h => hj (hz j h)
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter]
  congr 1
  · refine (Fintype.sum_of_injective o ho.injective _ _ (fun j hj => ?_) fun b => ?_).symm
    · simp [h0 j hj]
    · simp [ho.lt_iff_lt]
  · refine (Fintype.sum_of_injective o ho.injective _ _ (fun j hj => ?_) fun b => ?_).symm
    · simp [h0 j hj]
    · simp [ho.lt_iff_lt]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r)
  (ho : StrictMono o) (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (hd' : ∑ a, d (o a) = N)

include ho hz in

theorem deltaHalf_drop (g : Levi k fun j => Fin (d j)) :
    deltaHalf k (fun j => Fin (d j)) g = deltaHalf k (fun a => Fin (d (o a))) (dropHom d o g) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine (Fintype.prod_of_injective o ho.injective _ _ (fun j hj => ?_) fun a => ?_).symm
  · have hj0 : d j = 0 := by_contra fun h => hj (hz j h)
    have : IsEmpty (Fin (d j)) := by rw [hj0]; infer_instance
    have h1 : Matrix.GeneralLinearGroup.det (g j) = 1 := Units.ext (by simp [Matrix.det_isEmpty])
    rw [h1, map_one]
  · rw [modExp_drop d o ho hz]
    rfl

include ho hz in

theorem parInd_comp_dropHom_equiv {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun a => Fin (d (o a))) W) :
    Nonempty ((parInd (stdBlocks d hd) (τ.comp (dropHom d o) : Representation ℂ (Levi k fun j => Fin (d j)) W)).Equiv
      (parInd (stdBlocks (fun a => d (o a)) hd') τ)) := by
  have key : ∀ (p : parab k (stdBlocks d hd)) (q : parab k (stdBlocks (fun a => d (o a)) hd')),
      (p : GL (Fin N) k) = q →
      twist (τ.comp (dropHom d o) : Representation ℂ (Levi k fun j => Fin (d j)) W) (deltaHalf k _)
          (leviProj k (stdBlocks d hd) p) =
        twist τ (deltaHalf k _) (leviProj k (stdBlocks (fun a => d (o a)) hd') q) := fun p q h => by
    refine LinearMap.ext fun v => ?_
    rw [twist_apply, twist_apply, deltaHalf_drop d o ho hz, dropHom_leviProj k d hd o ho hz hd' p q h]
    show _ • τ (dropHom d o _) v = _
    rw [dropHom_leviProj k d hd o ho hz hd' p q h]
  refine Placing.smInd_equiv 1
    (fun q => ⟨⟨q.1, (mem_parab_drop k d hd o ho hz hd' q.1).2 q.2⟩, by simp, key _ _ rfl⟩)
    (fun p => ⟨⟨p.1, (mem_parab_drop k d hd o ho hz hd' p.1).1 p.2⟩, by simp, (key _ _ rfl).symm⟩)

end Local

set_option maxHeartbeats 1000000 in

theorem prodIrr_drop : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL k) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr (fun a => y (o a)) hd')) := by
  intro k _ _ _ _ r r' N y hd o ho hz hd'
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv y o ho hz
  obtain ⟨χ⟩ := parInd_comp_dropHom_equiv (k := k) (fun j => (y j).1) hd o ho hz hd'
    (piTensor fun a => (y (o a)).rep)
  have e1 := parIndEquiv (stdBlocks (fun j => (y j).1) hd) φ
  have e2 := e1.trans χ
  unfold prodIrr multiProd
  exact ⟨e2⟩

end GlobalTheory.CompanionTheory.FineProd.ProdDrop

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterConjIsOpen
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.TopGroup

theorem inter_conj_isOpen :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G),
      IsOpen (J : Set G) → ∀ g : G,
        IsOpen ((J ⊓ J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro G _ _ _ J hJ g
  have hpre : ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
      = (fun x : G => g⁻¹ * x * g) ⁻¹' (J : Set G) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩
  have hcont : Continuous (fun x : G => g⁻¹ * x * g) := by fun_prop
  have h2 : IsOpen ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [hpre]; exact hJ.preimage hcont
  rw [Subgroup.coe_inf]
  exact hJ.inter h2

end GlobalTheory.CompanionTheory.TopGroup
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterleavingTwoColourEmbedding
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd

namespace GlobalTheory.CompanionTheory.WordProd.Intl

def consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) : Fin (m + 1) ↪o Fin (k + 1) :=
  OrderEmbedding.ofStrictMono
    (Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ)) (by
      intro a b hab
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => exact absurd hab (lt_irrefl _)
        | succ b => simp [Fin.succ_pos]
      | succ a =>
        induction b using Fin.cases with
        | zero => exact absurd hab (Fin.not_lt_zero _)
        | succ b => simpa using hab)

def shiftEmb {m k : ℕ} (σ : Fin m ↪o Fin k) : Fin m ↪o Fin (k + 1) :=
  OrderEmbedding.ofStrictMono (fun a => (σ a).succ) (fun a b h => by simpa using h)

@[simp] theorem consEmb_zero {m k : ℕ} (σ : Fin m ↪o Fin k) : consEmb σ 0 = 0 := by
  first
    | rfl
    | exact Fin.cons_zero (α := fun _ => Fin (k + 1)) _ _
    | (show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) 0 = 0; simp)

@[simp] theorem consEmb_succ {m k : ℕ} (σ : Fin m ↪o Fin k) (a : Fin m) :
    consEmb σ a.succ = (σ a).succ := by
  first
    | rfl
    | exact Fin.cons_succ (α := fun _ => Fin (k + 1)) _ _ _
    | (show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) a.succ = (σ a).succ; simp)

@[simp] theorem shiftEmb_apply {m k : ℕ} (σ : Fin m ↪o Fin k) (a : Fin m) :
    shiftEmb σ a = (σ a).succ := rfl

theorem zero_mem_range_consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) :
    (0 : Fin (k + 1)) ∈ Set.range (consEmb σ) := ⟨0, consEmb_zero σ⟩

theorem succ_mem_range_consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) (j : Fin k) :
    j.succ ∈ Set.range (consEmb σ) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨a, ha⟩
    cases a using Fin.cases with
    | zero =>
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero] at ha
      exact absurd ha.symm (Fin.succ_ne_zero j)
    | succ a =>
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ] at ha
      exact ⟨a, Fin.succ_injective _ ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.succ, GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ σ a⟩

theorem succ_mem_range_shiftEmb {m k : ℕ} (σ : Fin m ↪o Fin k) (j : Fin k) :
    j.succ ∈ Set.range (shiftEmb σ) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨a, ha⟩
    rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at ha
    exact ⟨a, Fin.succ_injective _ ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply σ a⟩

theorem interleave_embeddings : ∀ {T : Type 1} {u v w : List T}, Zc.Comb.Interleave u v w →
    ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length)
      (σ₁ : Fin v.length ↪o Fin w.length),
      (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧
      (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) := by
  intro T u v w h
  induction h with
  | nil =>
    refine ⟨fun j => Fin.elim0 j, (OrderIso.refl _).toOrderEmbedding,
      (OrderIso.refl _).toOrderEmbedding, ?_, ?_, ?_, ?_⟩ <;> intro j <;> exact Fin.elim0 j
  | @left a u v w _ ih =>
    obtain ⟨r, σ₀, σ₁, h0, h1, hu, hv⟩ := ih
    refine ⟨(Fin.cons (0 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₀,
      GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₁, ?_, ?_, ?_, ?_⟩
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero, true_iff]
        exact GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₀
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]
        exact h0 j
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero]
        constructor
        · intro hc
          exact absurd hc (by decide)
        · rintro ⟨x, hx⟩
          rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at hx
          exact absurd hx (Fin.succ_ne_zero _)
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]
        exact h1 j
    · intro x
      obtain rfl | ⟨x, rfl⟩ := Fin.eq_zero_or_eq_succ (n := u.length) x
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]
        simp
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]
        first
          | exact hu x
          | simpa using hu x
    · intro x
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]
      first
        | exact hv x
        | simpa using hv x
  | @right a u v w _ ih =>
    obtain ⟨r, σ₀, σ₁, h0, h1, hu, hv⟩ := ih
    refine ⟨(Fin.cons (1 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₀,
      GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₁, ?_, ?_, ?_, ?_⟩
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero]
        constructor
        · intro hc
          exact absurd hc (by decide)
        · rintro ⟨x, hx⟩
          rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at hx
          exact absurd hx (Fin.succ_ne_zero _)
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]
        exact h0 j
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero, true_iff]
        exact GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₁
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]
        exact h1 j
    · intro x
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]
      first
        | exact hu x
        | simpa using hu x
    · intro x
      obtain rfl | ⟨x, rfl⟩ := Fin.eq_zero_or_eq_succ (n := v.length) x
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]
        simp
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]
        first
          | exact hv x
          | simpa using hv x

end GlobalTheory.CompanionTheory.WordProd.Intl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvF
section
noncomputable section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.TrPassage

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

def invF (r : Matrix.unitaryGroup (Fin n) ℂ →* (F →L[ℂ] F)) (E : KMod n) :
    Submodule ℂ ((E.V →L[ℂ] ℂ) →L[ℂ] F) where
  carrier := {t | ∀ k ξ, t (ξ ∘L E.ρ k⁻¹) = r k (t ξ)}
  add_mem' {a b} ha hb k ξ := by
    simp only [ContinuousLinearMap.add_apply, map_add]
    rw [ha k ξ, hb k ξ]
  zero_mem' k ξ := by simp
  smul_mem' c a ha k ξ := by
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    rw [ha k ξ]

def chiT (E : KMod n) (T : E.V →L[ℂ] E.V) (k : Matrix.unitaryGroup (Fin n) ℂ) : ℂ :=
  LinearMap.trace ℂ E.V ((E.ρ k * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V)

end GlobalTheory.CompanionTheory.TrPassage
end
end

