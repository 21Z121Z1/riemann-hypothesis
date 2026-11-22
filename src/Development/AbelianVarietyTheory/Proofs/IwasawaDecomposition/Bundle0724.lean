import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0966
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStarDepthSetThroughRadicalFreePresentation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions.TH

set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.Mem.GridMove
open GlobalTheory.ChiGrid
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {T : Type}

def plC {L : Formalism.IndefR.Links.LevCh a.D T} (P : Places L) : Places (levCh b L) where
  v0 := (by with_unfolding_all exact (P.v0 :))
  basePlace_over_qZero := (by with_unfolding_all exact (P.basePlace_over_qZero :))
  w := (by with_unfolding_all exact (P.w :))
  w_over := (by with_unfolding_all exact (P.w_over :))
  w_split := (by with_unfolding_all exact (P.w_split :))
  w_g := (by with_unfolding_all exact (P.w_g :))
  w_de := (by with_unfolding_all exact (P.w_de :))
  w_Q := (by with_unfolding_all exact (P.w_Q :))
  levelPlace_ne_basePlace := (by with_unfolding_all exact (P.levelPlace_ne_basePlace :))

def chC {L : Formalism.IndefR.Links.LevCh a.D T} {P : Places L} {c : ℝ} (X : Chars P c) : Chars (plC b P) c where
  chiH := (by with_unfolding_all exact (X.chiH :))
  chi := (by with_unfolding_all exact (X.chi :))
  chi_eq := (by with_unfolding_all exact (X.chi_eq :))
  triv := (by with_unfolding_all exact (X.triv :))
  inf := (by with_unfolding_all exact (X.inf :))
  unr := (by with_unfolding_all exact (X.unr :))
  lev1 := (by with_unfolding_all exact (X.lev1 :))
  wild := (by with_unfolding_all exact (X.wild :))
  lev0 := (by with_unfolding_all exact (X.lev0 :))

def lsC (X : LSp a.D) : LSp b.D := ⟨(by with_unfolding_all exact (X.sp :)), (by with_unfolding_all exact (X.lat :))⟩

theorem isVC {X : LSp a.D} {ν q : ℕ} (h : X.IsV ν q) : (lsC b X).IsV ν q :=
  ⟨(by with_unfolding_all exact (h.rank :)), (by with_unfolding_all exact (h.sigOK :)), (by with_unfolding_all exact (h.sig :)), (by with_unfolding_all exact (h.sd :))⟩

def adC {A B' : HSp a.D} {c : ℕ} {ε : a.D.host.E} (d : HermitianOrthogonalExtensionData A B' c ε) :
    @HermitianOrthogonalExtensionData b.D ((A)) ((B')) c ((ε)) where
  ι := (by with_unfolding_all exact (d.ι :))
  isom := (by with_unfolding_all exact (d.isom :))
  a := (by with_unfolding_all exact (d.a :))
  gram := (by with_unfolding_all exact (d.gram :))
  perp := (by with_unfolding_all exact (d.perp :))
  rank := (by with_unfolding_all exact (d.rank :))

section V
open scoped nonZeroDivisors
variable {L : Formalism.IndefR.Links.LevCh a.D T} (Vs : ℕ → ℕ → LSp a.D) (Xs : ℕ → LSp a.D)

def gridColumnVertexDecompTransport (P : ℕ → LSp a.D) : ∀ (i : ℕ) (_ : 1 ≤ i) (_ : HermitianOrthogonalExtensionData (P i).sp (vtxOf L Vs i 0).sp (i - 1) (-1)),
    HermitianOrthogonalExtensionData (lsC b (P i)).sp (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) i 0).sp (i - 1) (-1)
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridStaircaseLattice_firstColumn_transportStages (P : ℕ → LSp a.D) : ∀ (i : ℕ) (h : 1 ≤ i) (d : HermitianOrthogonalExtensionData (P i).sp (vtxOf L Vs i 0).sp (i - 1) (-1))
    (𝔟 : Fin (i - 1) → FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E),
    (vtxOf L Vs i 0).lat = d.lat (P i).lat 𝔟 →
    (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) i 0).lat = (gridColumnVertexDecompTransport b Vs P i h d).lat (lsC b (P i)).lat ((𝔟))
  | 0, h, _, _, _ => absurd h (by omega)
  | _ + 1, _, _, _, e => (e)

def gridInteriorVertexDecompTransport (j : ℕ) : ∀ (n : ℕ) (_ : j + 1 < n) (_ : HermitianOrthogonalExtensionData (Xs (j + 1)).sp (vtxOf L Vs n (j + 1)).sp (n - 1 - (j + 1)) (-1)),
    HermitianOrthogonalExtensionData (lsC b (Xs (j + 1))).sp (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n (j + 1)).sp (n - 1 - (j + 1)) (-1)
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridLastRowVertexLattice_transportStages (j : ℕ) : ∀ (n : ℕ) (h : j + 1 < n) (d : HermitianOrthogonalExtensionData (Xs (j + 1)).sp (vtxOf L Vs n (j + 1)).sp (n - 1 - (j + 1)) (-1))
    (𝔟 : Fin (n - 1 - (j + 1)) → FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E),
    (vtxOf L Vs n (j + 1)).lat = d.lat (Xs (j + 1)).lat 𝔟 →
    (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n (j + 1)).lat = (gridInteriorVertexDecompTransport b Vs Xs j n h d).lat (lsC b (Xs (j + 1))).lat ((𝔟))
  | 0, h, _, _, _ => absurd h (by omega)
  | _ + 1, _, _, _, e => (e)

def gridDiagonalVertexDecompTransport (X0 : LSp a.D) : ∀ (n : ℕ) (_ : 1 ≤ n) (_ : HermitianOrthogonalExtensionData (vtxOf L Vs n n).sp (xOf X0 Xs n).sp 1 1),
    HermitianOrthogonalExtensionData (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n n).sp (xOf (lsC b X0) (fun j => lsC b (Xs j)) n).sp 1 1
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridTopVertexLattice_transportStages (X0 : LSp a.D) : ∀ (n : ℕ) (h : 1 ≤ n) (d : HermitianOrthogonalExtensionData (vtxOf L Vs n n).sp (xOf X0 Xs n).sp 1 1),
    (xOf X0 Xs n).lat = d.lat (vtxOf L Vs n n).lat (fun _ => 1) →
    (xOf (lsC b X0) (fun j => lsC b (Xs j)) n).lat = (gridDiagonalVertexDecompTransport b Vs Xs X0 n h d).lat (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n n).lat (fun _ => 1)
  | 0, h, _, _ => absurd h (by omega)
  | _ + 1, _, _, e => (e)

end V

section W
open scoped nonZeroDivisors
variable {L : Formalism.IndefR.Links.LevCh a.D T}

def vtC {𝔞 𝔞' : FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E} (V : Vertices L 𝔞 𝔞') :
    Vertices (levCh b L) ((𝔞)) ((𝔞')) where
  Vs i j := lsC b (V.Vs i j)
  P i := lsC b (V.P i)
  Xs j := lsC b (V.Xs j)
  V_is i j h1 h2 h3 := (by with_unfolding_all exact ((isVC b (V.V_is i j h1 h2 h3)) :))
  P_is i h := (by with_unfolding_all exact ((isVC b (V.P_is i h)) :))
  X_is j h1 h2 := (by with_unfolding_all exact ((isVC b (V.X_is j h1 h2)) :))
  dec0 := (by with_unfolding_all exact ((adC b V.dec0) :))
  lat0 := (by with_unfolding_all exact (V.lat0 :))
  colDec i h h' := gridColumnVertexDecompTransport b V.Vs V.P i h (V.colDec i h h')
  colLat i h h' := (by with_unfolding_all exact ((gridStaircaseLattice_firstColumn_transportStages b V.Vs V.P i h (V.colDec i h h') _ (V.colLat i h h')) :))
  rowDecS j h := (by with_unfolding_all exact ((gridInteriorVertexDecompTransport b V.Vs V.Xs j a.D.R.m h (V.rowDecS j h)) :))
  rowLat j h := (by with_unfolding_all exact ((gridLastRowVertexLattice_transportStages b V.Vs V.Xs j a.D.R.m h (V.rowDecS j h) _ (V.rowLat j h)) :))
  topDec := (by with_unfolding_all exact ((gridDiagonalVertexDecompTransport b V.Vs V.Xs (V.P a.D.R.m) a.D.R.m (by have := a.D.R.two_le_m; omega) V.topDec) :))
  topLat := (by with_unfolding_all exact ((gridTopVertexLattice_transportStages b V.Vs V.Xs (V.P a.D.R.m) a.D.R.m (by have := a.D.R.two_le_m; omega) V.topDec V.topLat) :))

def gdC {sc : Consts} (G : GridData L sc) : GridData (levCh b L) sc where
  pl := plC b G.pl
  ch := chC b G.ch
  sp := (by with_unfolding_all exact ((vtC b G.sp) :))

end W

section Y
variable {L : Formalism.IndefR.Links.LevCh a.D T}

theorem listPin_upL (S' : SStage B C a.W) (Nn : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (hh : B.Word → ℝ) (c bb : ℝ)
    (h : ListPin a.D L c bb) : ListPin (upL a S' Nn hh).D (levCh (upL a S' Nn hh) L) c bb := by
  obtain ⟨G, h1, h2⟩ := h
  exact ⟨gdC _ G, ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩, (by with_unfolding_all exact (h2 :))⟩
end Y

set_option maxHeartbeats 4000000 in

theorem listPin_rowsSame : ∀ (cDep b : ℝ) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep b → ListPin (w.st (upL Z S' N h)).toD7 t'.r.z.R.toRealDat.toLevCh cDep b := by
  intro cDep b K B f T w Z Wt S' N h p0 t p0' t' hs hp
  cases t' with | mk hX' r' => ?_
  cases r' with | mk z' => ?_
  cases z' with | @mk Xg' tr' core' alg' alg_eq' R' => ?_
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  clear hs
  change Xg' = t.r.z.Xg at hXg
  change tr' = t.r.z.tr at htr
  subst hXg htr
  change HEq core' _ at hcore
  have hc := eq_of_heq hcore
  subst hc
  have ha : alg' = GlobalTheory.Mem.R3.Tr.alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(upL Z S' N h).W, (upL Z S' N h).V, (upL Z S' N h).S, (upL Z S' N h).N, (upL Z S' N h).G⟩ t.r.z.alg := by
    apply Algebra.algebra_ext
    intro r
    apply (w.st (upL Z S' N h)).B.embLL.injective
    exact (by with_unfolding_all exact (((alg_eq' r).trans (t.r.z.alg_eq r).symm) :))
  subst ha
  change HEq R' _ at hR
  have hR2 := eq_of_heq hR
  subst hR2
  exact (by with_unfolding_all exact ((listPin_upL (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) S' N h cDep b hp) :))

end GlobalTheory.Mem.GridMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigISupEqTopOfSep
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.heckeEig_iSup_eq_top_of_sep {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Finite X]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) :
    ⨆ x, heckeEig T act x = ⊤ := by
  classical
  have := Fintype.ofFinite X
  have hs' : ∀ x y : X, ∃ f : T, x ≠ y → (f : X → O) x ≠ (f : X → O) y := by
    intro x y
    by_cases h : x = y
    · exact ⟨1, fun h' => (h' h).elim⟩
    · obtain ⟨f, hf, hne⟩ := hsep x y h
      exact ⟨⟨f, hf⟩, fun _ => hne⟩
  choose s hs using hs'
  let E : X → T := fun x => ∏ y ∈ Finset.univ.erase x, (s x y - algebraMap O T ((s x y : X → O) y))
  have hE : ∀ x z, ((E x : T) : X → O) z = ∏ y ∈ Finset.univ.erase x, ((s x y : X → O) z - (s x y : X → O) y) := by
    intro x z
    simp [E, Subalgebra.coe_prod, Finset.prod_apply]
  let d : X → O := fun x => ((E x : T) : X → O) x
  have hd : ∀ x, d x ≠ 0 := by
    intro x
    simp only [d, hE]
    exact Finset.prod_ne_zero_iff.mpr fun y hy => sub_ne_zero.mpr (hs x y (Ne.symm (Finset.ne_of_mem_erase hy)))
  have hE0 : ∀ x z, z ≠ x → ((E x : T) : X → O) z = 0 := by
    intro x z hz
    rw [hE]
    exact Finset.prod_eq_zero (i := z) (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ _⟩) (sub_self _)
  have hmul : ∀ (g : T) x, g * E x = ((g : X → O) x) • E x := by
    intro g x
    apply Subtype.ext
    funext z
    by_cases hz : z = x
    · subst hz; simp
    · simp [hE0 x z hz]
  let F : X → O := fun x => ∏ x' ∈ Finset.univ.erase x, d x'
  let c : O := ∏ x, d x
  have hsum : ∑ x, F x • E x = algebraMap O T c := by
    apply Subtype.ext
    funext z
    rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single z]
    · simp only [F, c]
      show (∏ x' ∈ Finset.univ.erase z, d x') * d z = _
      rw [mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ z)]
      simp
    · intro x _ hx
      rw [hE0 x z (Ne.symm hx), mul_zero]
    · intro h; exact (h (Finset.mem_univ z)).elim
  let K := FractionRing O
  let ψ : T →ₐ[O] Module.End K (TensorProduct O K M) := (Module.End.baseChangeHom O K M).comp act
  have hψ : ∀ f, ψ f = (act f).baseChange K := fun f => rfl
  have hmem : ∀ x (m : TensorProduct O K M), ψ (E x) m ∈ heckeEig T act x := by
    intro x m
    simp only [heckeEig]
    refine Submodule.mem_iInf _ |>.mpr fun f => ?_
    rw [Module.End.mem_eigenspace_iff, ← hψ]
    rw [show ψ f (ψ (E x) m) = (ψ f * ψ (E x)) m from rfl, ← map_mul, hmul, map_smul,
      LinearMap.smul_apply, algebraMap_smul]
  have hc : algebraMap O K c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact Finset.prod_ne_zero_iff.mpr fun x _ => hd x
  refine eq_top_iff.mpr fun m _ => ?_
  have hcm : algebraMap O K c • m = ∑ x, F x • ψ (E x) m := by
    rw [algebraMap_smul]
    have := congrArg (fun f => ψ f m) hsum
    simp only [map_sum, map_smul, AlgHom.commutes] at this
    rw [LinearMap.sum_apply] at this
    simp only [LinearMap.smul_apply] at this
    rw [this, Module.algebraMap_end_apply]
  have : m = (algebraMap O K c)⁻¹ • (algebraMap O K c • m) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this, hcm]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun x _ => ?_)
  exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_iSup_of_mem x (hmem x m))

theorem eigSpan_of_record (D : D7) : D.nd.EigSpan :=
  fun i => GlobalTheory.heckeEig_iSup_eq_top_of_sep (D.nd.T i) (D.nd.act i) (D.nd.T_sep i)

theorem ptSt_eigSpan : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => D'.nd.EigSpan := by
  intro hL _
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l
  exact ⟨fun _ => ∅, fun L _ => eigSpan_of_record _⟩

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGaloisStageFitsOfSameCentreActions
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.SwapN

open GlobalTheory.Mem.Top.TypesTrue

theorem heq_apply_cast {X : Type*} {P P' : Fin 2 → Type} (h : P = P') {a : ∀ k, P k → X} {a' : ∀ k, P' k → X}
    (ha : HEq a a') (k : Fin 2) (v : P k) : a' k (cast (congrFun h k) v) = a k v := by
  subst h
  obtain rfl := eq_of_heq ha
  rfl

theorem cen_transport {r : ℕ} {g : Fin 2 → ℕ} {P P' : Fin 2 → Type} (h : P = P') {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {c : ∀ i, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i)}
    {c' : ∀ i, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i)}
    (hc : HEq c c')
    (e : (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1))) ≃* (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))
    (he : ∀ x k v, e x ⟨k, cast (congrFun h k) v⟩ = x ⟨k, v⟩) (i : ι) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))))
    (z₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))) (hz : ∀ x, (z₁ : MonoidAlgebra ℂ _).coeff (e x) =
      (z : MonoidAlgebra ℂ _).coeff x) : c i z = c' i z₁ := by
  subst h
  obtain rfl := eq_of_heq hc
  have he' : ∀ x, e x = x := fun x => funext fun kv => he x kv.1 kv.2
  congr 1
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun x => ?_
  have := hz x
  rw [he'] at this
  exact this.symm

theorem cen_transport₂ {r : ℕ} {g : Fin 2 → ℕ} {P P' : Fin 2 → Type} (h : P = P') {ι κ : Type*} {E : ι → κ → Type*}
    [∀ i j, AddCommGroup (E i j)] [∀ i j, Module ℂ (E i j)]
    {c : ∀ i j, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i j)}
    {c' : ∀ i j, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i j)}
    (hc : HEq c c')
    (e : (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1))) ≃* (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))
    (he : ∀ x k v, e x ⟨k, cast (congrFun h k) v⟩ = x ⟨k, v⟩) (i : ι) (j : κ) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))))
    (z₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))) (hz : ∀ x, (z₁ : MonoidAlgebra ℂ _).coeff (e x) =
      (z : MonoidAlgebra ℂ _).coeff x) : c i j z = c' i j z₁ := by
  subst h
  obtain rfl := eq_of_heq hc
  have he' : ∀ x, e x = x := fun x => funext fun kv => he x kv.1 kv.2
  congr 1
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun x => ?_
  have := hz x
  rw [he'] at this
  exact this.symm

theorem mem_center_map {G G' : Type*} [Monoid G] [Monoid G'] (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ] MonoidAlgebra ℂ G')
    {a : MonoidAlgebra ℂ G} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : φ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G') := by
  rw [Subalgebra.mem_center_iff] at ha ⊢
  intro b
  obtain ⟨b, rfl⟩ := φ.surjective b
  rw [← map_mul, ← map_mul, ha b]

end GlobalTheory.Mem.R3.Rw.SwapN

namespace GlobalTheory.Mem.R3.Rw.SwapN

theorem fits_swap : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → N.nd.PlG = x.o.N.nd.PlG → HEq N.naut.plGw x.o.N.naut.plGw → HEq N.ntypes.cenAmb x.o.N.ntypes.cenAmb → HEq N.ntypes.cenMt x.o.N.ntypes.cenMt → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR := by
  intro K B f T w P x N hG hP hw hA hM
  have hG' : GrpTrue x.o.N f := x.fits.grp
  obtain ⟨⟨plg, hplg⟩, hidem, hcen⟩ := x.fits.grpAt
  let e := grpEquiv N.naut x.o.N.naut
  have hco : ∀ g, x.o.N.ntypes.e0.coeff (e g) = N.ntypes.e0.coeff g := GrpTrue.typeIdempotent_coeff_across_layers hG hG'
  let φ := MonoidAlgebra.domCongr ℂ ℂ e
  have hφ : ∀ (a : MonoidAlgebra ℂ (G0g N.nd)) g, (φ a).coeff (e g) = a.coeff g := by
    intro a g
    simp [φ]
  have he0 : N.ntypes.e0 = φ.symm x.o.N.ntypes.e0 := by
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    show _ = (MonoidAlgebra.domCongr ℂ ℂ e.symm x.o.N.ntypes.e0).coeff g
    rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm, hco]
  have hpe : ∀ k v, plEquiv N.naut x.o.N.naut k v = cast (congrFun hP k) v := by
    intro k v
    show (plF x.o.N.naut k).symm (plF N.naut k v) = _
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [plF_apply, plF_apply, heq_apply_cast hP hw k v]
  have he : ∀ (g : G0g N.nd) k v, e g ⟨k, cast (congrFun hP k) v⟩ = g ⟨k, v⟩ := by
    intro g k v
    rw [grpEquiv_apply, ← hpe, Equiv.symm_apply_apply]
  refine ⟨⟨⟨(Equiv.sigmaCongrRight fun k => plEquiv N.naut x.o.N.naut k).trans plg, fun kv => ?_⟩, ?_, ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := hplg ⟨kv.1, plEquiv N.naut x.o.N.naut kv.1 kv.2⟩
    refine ⟨?_, h2⟩
    exact h1.trans (TypesTrue.plGw_plEquiv hG hG' kv.1 kv.2)
  · show IsIdempotentElem N.ntypes.e0
    rw [he0]
    exact hidem.map φ.symm
  · show N.ntypes.e0 ∈ _
    rw [he0]
    exact mem_center_map φ.symm hcen
  · rintro eR ⟨plg1, iso1, hpl1, hact1⟩
    have hstd : StdIso (w.st x.o.Z) w.px (eR.trans e) := by
      refine ⟨(Equiv.sigmaCongrRight fun k => (plEquiv N.naut x.o.N.naut k).symm).trans plg1,
        fun kv => iso1 ⟨kv.1, (plEquiv N.naut x.o.N.naut kv.1).symm kv.2⟩, fun kv => ?_, fun g kv => ?_⟩
      · refine (hpl1 ⟨kv.1, (plEquiv N.naut x.o.N.naut kv.1).symm kv.2⟩).trans ?_
        have := TypesTrue.plGw_plEquiv hG hG' kv.1 ((plEquiv N.naut x.o.N.naut kv.1).symm kv.2)
        exact ((congrArg (x.o.N.naut.plGw kv.1) (Equiv.apply_symm_apply (plEquiv N.naut x.o.N.naut kv.1) kv.2)).symm.trans
          this).symm
      · exact hact1 g _
    have hc := x.fits.cen _ hstd
    have hz1 : ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N.nd))), φ (z : MonoidAlgebra ℂ (G0g N.nd)) ∈
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g x.o.N.nd)) := fun z => mem_center_map φ z.2
    refine ⟨fun μ z z' hz xx => ?_, fun μ j z z' hz xx => ?_⟩
    · have h1 := hc.amb μ ⟨_, hz1 z⟩ z' (fun g => by
        show _ = (φ (z : MonoidAlgebra ℂ (G0g N.nd))).coeff (e (eR g))
        exact (hz g).trans (hφ _ _).symm) xx
      rw [cen_transport hP hA e he μ z ⟨_, hz1 z⟩ (fun g => hφ _ g)]
      exact h1
    · have h1 := hc.mt μ j ⟨_, hz1 z⟩ z' (fun g => by
        show _ = (φ (z : MonoidAlgebra ℂ (G0g N.nd))).coeff (e (eR g))
        exact (hz g).trans (hφ _ _).symm) xx
      rw [cen_transport₂ hP hM e he μ j z ⟨_, hz1 z⟩ (fun g => hφ _ g)]
      exact h1

end GlobalTheory.Mem.R3.Rw.SwapN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeReadingEigenvaluePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatHeckeBall

set_option maxHeartbeats 1600000 in

theorem ratHecke_keeps_ball : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ (j k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ j → j ≤ (Dof x).R.m → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → k ≤ (Dof x).R.r → ∀ la : HeightOneSpectrum (𝓞 (SOf x).Ks), (∀ q : ℕ, q.Prime → (q : 𝓞 (Dof x).host.E) ∈ Pl.asIdeal → (q : 𝓞 (SOf x).Ks) ∉ la.asIdeal) → ∀ (f : (SOf x).WL j) (hf : f ∈ ((SOf x).A j).WK) (hg : hL' j k Pl f ∈ ((SOf x).A j).WK), (∀ y, ((SOf x).A j).nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, ((SOf x).A j).nrm la y ⟨hL' j k Pl f, hg⟩ ≤ 1 := by
  intro hLL hDec hI hT hRT
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine ((hId.and (ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x _ hL' hstab hRd j k v hj1 hj2 hsp hPS hk la hla g hg hhg hball
  obtain ⟨hHo, -⟩ := H.1.2 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := H.2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
    exact hs.to_subtype
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hS := GlobalTheory.T.heckeOperator_preserves_supLattice_realSide hDec hI hT hRT (Dof x) X (idxOf (Dof x) j)
  have hlow : ∀ p ∈ lowAll (Dof x), p ≠ 0 → ((p : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro p hp hp0 hm
    apply hPS
    rw [SbD, Set.Finite.mem_toFinset]
    exact ⟨p, hp, hp0, hm⟩
  have hgP : ∀ kk : Fin 2, (((Dof x).host.g kk : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := fun kk =>
    hlow _ (by fin_cases kk <;> simp [lowAll]) ((Dof x).host.g_prime kk).ne_zero
  have hso : Bridge.SplitOff v (X.R.Sb : Set (Formalism.L2.DIV.Pl (Dof x).host.E)) := by
    have hAll : X.R.Sb = X.R.Pg := X.char.allPl
    have hPg := X.char.lev.Pg
    refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hsp, fun h => ?_, fun Q hQ h => ?_⟩
    · rw [Finset.mem_coe, hAll] at h
      obtain ⟨kk, hkk⟩ := (hPg v).1 h
      exact hgP kk (GlobalTheory.StepLaw.typePrime_mem_of_div hkk)
    · rw [Finset.mem_coe, hAll] at hQ
      obtain ⟨kk, hkk⟩ := (hPg Q).1 hQ
      have hm := GlobalTheory.StepLaw.typePrime_mem_of_div hkk
      rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hm
      exact hgP kk hm
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt X.char.lev X.char.fam (idxOf (Dof x) j) hso hk
  have hg01 : (((Dof x).host.g 0 * (Dof x).host.g 1 : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro hm
    rw [Nat.cast_mul] at hm
    rcases v.isPrime.mem_or_mem hm with h | h
    exacts [hgP 0 h, hgP 1 h]
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData X.R.toRealDat (idxOf (Dof x) j) v k α Rc := ⟨hso, hg01, hk, ha, hR⟩
  have hkd : HkDat x.m.z.R (SbD (Dof x)) (idxOf (Dof x) j) k v α Rc :=
    ⟨hsp, hPS, hlow 2 (by simp [lowAll, lowPr]) two_ne_zero, hk, ha, hR⟩
  have e : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC X.R.toRealDat (idxOf (Dof x) j) v k = hkNorm x.m.z.R (idxOf (Dof x) j) k v := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC, hkNorm, inv_pow]
    all_goals rfl
  have hK := hS v k α Rc hd (hL' j k v) (fun y => by rw [e]; exact hRd j k v α Rc hj1 hj2 hkd y)
    (fun y hy => hstab j hj1 hj2 k v y hy) la hla
  exact hK.sup ⟨g, hg⟩ hball

end GlobalTheory.RatHeckeBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricGStatement
section
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDeriv_chernConnection_inverseSymmetricGram : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → ∀ ξ η, GlobalTheory.HermFrame.mdel (fun x => GlobalTheory.HermFrame.conn (fun y => (H y)⁻¹) x η) z ξ - GlobalTheory.HermFrame.mdel (fun x => GlobalTheory.HermFrame.conn (fun y => (H y)⁻¹) x ξ) z η = -(GlobalTheory.HermFrame.conn H z η * GlobalTheory.HermFrame.conn H z ξ - GlobalTheory.HermFrame.conn H z ξ * GlobalTheory.HermFrame.conn H z η)ᵀ := by
  first | exact @GlobalTheory.HermFrame.mdel_conn_inv_sub | exact GlobalTheory.HermFrame.mdel_conn_inv_sub | (intros; apply GlobalTheory.HermFrame.mdel_conn_inv_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStarDepthSetThroughRadicalFreePresentationStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_starDepthSet_through_radicalFree_presentation : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X) (t : ℝ), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → 0 < t → B - t • toReal v ∈ rcone γ → ∀ (n : ℕ) (π : (Fin n → O) →ₗ[O] X), Function.Surjective π → t ∈ depthSet bar ψ w n (fun a b => B (π a) (π b)) := by
  first | exact @GlobalTheory.PolFan.mem_depthSet_of_rcone | exact GlobalTheory.PolFan.mem_depthSet_of_rcone | (intros; apply GlobalTheory.PolFan.mem_depthSet_of_rcone <;> assumption)
end

