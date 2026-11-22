import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0754
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0994
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0755
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0772
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0757
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0705

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesOfAdmissibleTwistStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_places_of_admissible_twist : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → ¬ (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∧ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ (∀ kv, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv)).v ≠ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') := by
  first | exact @GlobalTheory.SepPlaces.cell_places_sep | exact GlobalTheory.SepPlaces.cell_places_sep | (intros; apply GlobalTheory.SepPlaces.cell_places_sep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellQPlacesOfAdmissibleTwistStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_q_places_of_admissible_twist : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' l.b.Bs.exp.sgnT u = 1) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ((Dof x).ntw.delta i) P'' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) u = 1) := by
  first | exact @GlobalTheory.LevCmp.tameVal_wild_one | exact GlobalTheory.LevCmp.tameVal_wild_one | (intros; apply GlobalTheory.LevCmp.tameVal_wild_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellRayInConeOfMarkedFormPiecesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_ray_in_cone_of_marked_form_pieces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell H.bar φ δ₀ → LinearIndependent ℤ δ₀ →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] (π : X₀ →ₗ[𝓞 E] Y), Function.Surjective π → ∀ (τ : 𝓞 E ≃+* 𝓞 E) (f : X →+ Y), τ H.w0 = H.w0 →
    Function.Surjective f → (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y, (∀ i, 0 < t i → pull π (u i) = δ₀ i) →
  ∀ β : LinearMap.BilinForm ℤ X, (∀ (x y : X) (x₀ y₀ : X₀), π x₀ = f x → π y₀ = f y → β x y = v x₀ y₀) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧
    toReal (δ j) = ∑ i, a i • toReal (pullAdd f (u i)) := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_coord_pullAdd_of_pos | exact GlobalTheory.PolFan.OrbMark.exists_coord_pullAdd_of_pos | (intros; apply GlobalTheory.PolFan.OrbMark.exists_coord_pullAdd_of_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitNontrivialAt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameTypes

open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.CenFrame

set_option maxHeartbeats 4000000 in

theorem mtInput_of {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (M' : MtFam D') (hM : HEq (mtL nt.L nt.M) M') :
    ∃ tup Q, MtInput D' M' tup Q := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have hm : mtL L M = M' := eq_of_heq hM
  subst hm
  exact ⟨tp.tup, C.Q, { mt with }⟩

def IsBlockUpperUnipotentMatrix {k : Type} [CommRing k] {n : ℕ} (r : ℕ) (x : GL (Fin n) k) : Prop :=
  ∀ i j : Fin n, (r ≤ i.val → j.val < r → x.val i j = 0) ∧ (i.val < r → j.val < i.val → x.val i j = 0) ∧
    (i.val < r → i = j → x.val i j = 1)

theorem blkUni_one {k : Type} [CommRing k] {n : ℕ} (r : ℕ) : IsBlockUpperUnipotentMatrix r (1 : GL (Fin n) k) := by
  intro i j
  refine ⟨fun h1 h2 => ?_, fun _ h2 => ?_, fun _ h2 => ?_⟩
  · rw [Units.val_one, Matrix.one_apply_ne]; rintro rfl; omega
  · rw [Units.val_one, Matrix.one_apply_ne]; rintro rfl; omega
  · rw [Units.val_one, h2, Matrix.one_apply_eq]

theorem IsBlockUpperUnipotentMatrix.blk2 {k : Type} [CommRing k] {n r : ℕ} {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) : x ∈ blockTri (blk2 r) := by
  refine mem_blockTri.2 fun i j hij => ?_
  unfold Formalism.L2.DIV.blk2 at hij
  refine (h i j).1 ?_ ?_ <;> split_ifs at hij <;> omega

theorem IsBlockUpperUnipotentMatrix.blkOf {k : Type} [CommRing k] {n r t : ℕ} (hn : n ≤ r + t) {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) :
    x ∈ blockTri (blkOf r t) := by
  refine mem_blockTri.2 fun i j hij => ?_
  unfold Formalism.L2.DIV.blkOf at hij
  have hi := i.2
  by_cases h1 : i.val < r
  · rw [if_pos h1] at hij; omega
  · rw [if_neg h1, Nat.div_eq_of_lt (show i.val - r < t by omega)] at hij
    refine (h i j).1 (by omega) ?_
    by_contra h2
    rw [if_neg h2] at hij
    exact absurd hij (not_lt.2 (Nat.succ_le_succ (Nat.zero_le _)))

theorem IsBlockUpperUnipotentMatrix.unip {k : Type} [CommRing k] {n r : ℕ} (hr : r ≤ n) {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) :
    upperLeftBlock hr x ∈ unip k r := by
  refine ⟨mem_blockTri.2 fun i j hij => ?_, fun i => ?_⟩
  · rw [upper_block_val_submatrix hr h.blk2]
    exact (h _ _).2.1 i.2 hij
  · rw [upper_block_val_submatrix hr h.blk2]
    exact (h _ _).2.2 i.2 rfl

variable {D : D7}

theorem isConjPl_of_under (s : SplitPlace D.host.E) {PP : PlE D.host} (hne : PP ≠ s.w)
    (h : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) PP = s.v) : Formalism.IndefR.Lev.IsConjPl (D := D) PP s.w := by
  rcases Formalism.L2.eq_or_eq_conjPlE s.w PP ((congrArg HeightOneSpectrum.asIdeal h).trans s.w_under.symm) with e | e
  · exact absurd e hne
  · intro c hc
    rw [e, Formalism.L2.mem_conjPlE] at hc
    refine ⟨_, hc, ?_⟩
    rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.TypePlaces.star_eq_conj, GlobalTheory.SplitPlaceOver.host_conj_eq']

theorem mem_level {V : TH.HSp D} {n : ℕ} (hn : V.rank = n) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : Formalism.IndefR.principalLevelFrame.RowPsi V n} (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hrt : V.rank ≤ L.r + L.t)
    (hH : ∀ g : G0 L.Pg L.r, (∀ PP, g PP ∈ unip (kP PP.1) L.r) → g ∈ L.P.H)
    (s : SplitPlace D.host.E) (hsep : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP s.w)
    {φ : Os s →+* kP s.w} {b : GL (Fin n) (kP s.w)} (hfr : FrameRed hn P β s φ b)
    {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n) (hT : TrivOutside {s.v} κ) {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) :
    (IsBlockUpperUnipotentMatrix L.r (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹) → P.ψ κ ∈ Formalism.IndefR.Links.levS V β L) ∧
    (Matrix.GeneralLinearGroup.map φ y = 1 →
      P.ψ κ ∈ Formalism.IndefR.Links.levS V β L ∧ Formalism.IndefR.Lev.levChi V β L (P.ψ κ) = 1) := by
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ s.w → redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
    intro PP hPP hne
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {PP.under (𝓞 D.host.F)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    exact GlobalTheory.NonSplitLevel.projV_eq_one hP κ PP (hT _ fun e => hsep PP hPP (isConjPl_of_under s hne e))
  have hent : ∀ i j : Fin V.rank, (redFn β s.w (Formalism.IndefR.Lev.finE V (P.ψ κ))).val i j =
      (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val (Fin.cast hn i) (Fin.cast hn j) :=
    fun i j => hfr κ hU y hy (Fin.cast hn i) (Fin.cast hn j)
  refine ⟨fun hb => ?_, fun h1 => ?_⟩
  · have hall : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → IsBlockUpperUnipotentMatrix L.r (redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ))) := by
      intro PP hPP
      by_cases e : PP = s.w
      · subst e
        intro i j
        rw [hent]
        have hb' := hb (Fin.cast hn i) (Fin.cast hn j)
        exact ⟨hb'.1, hb'.2.1, fun h1 h2 => hb'.2.2 h1 (congrArg _ h2)⟩
      · rw [hred PP hPP e]; exact blkUni_one _
    exact ⟨P.into κ, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hS, fun PP h => (hall PP (Or.inl h)).blkOf hrt,
      fun PP h => (hall PP (Or.inr h)).blk2⟩, hH _ fun PP => (hall PP.1 (Or.inl PP.2)).unip L.hr⟩⟩
  · have hall : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
      intro PP hPP
      by_cases e : PP = s.w
      · subst e
        refine Units.ext (Matrix.ext fun i j => ?_)
        rw [hent, h1, mul_one, mul_inv_cancel, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
        exact if_congr (Fin.cast_injective hn).eq_iff rfl rfl
      · exact hred PP hPP e
    refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hS hall⟩, ?_⟩
    unfold Formalism.IndefR.Lev.levChi
    rw [GlobalTheory.LevSplit.levFn_eq_one β L _ hall, Units.val_one]

section Read
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}

set_option maxHeartbeats 1000000 in

theorem exists_fn (ad : MtAd Y M) (μ : D.what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 D μ) (k : Fin D.R.m)
    (hnt : Nontrivial (D.what₂.Mt μ ((k : ℕ) + 1))) :
    ∃ f : GAf D.host.E D.R.nV → ℂ, f ≠ 0 ∧
      (∀ κ (h : κ ∈ (M μ (k.1 + 1) (by omega) (by omega)).J) g,
        f (g * κ) = (((M μ (k.1 + 1) (by omega) (by omega)).χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
      ∀ κ, (ad.PV k).ψ κ ∈ levS _ (R.toRealDat.βV k)
          (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) →
        ∀ g, f (g * κ) = levChi _ (R.toRealDat.βV k)
          (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) ((ad.PV k).ψ κ) * f g := by
  obtain ⟨x, hx⟩ := exists_ne (0 : D.what₂.Mt μ ((k : ℕ) + 1))
  have hr : (M μ (k.1 + 1) (by omega) (by omega)).real x ≠ 0 := fun e =>
    hx ((M μ (k.1 + 1) _ _).real_inj (e.trans (map_zero _).symm))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hr
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hg₀
  have hm : (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real x ∈ NG.TypeSp (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).wt.ρ
      (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).J (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).χ :=
    (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real_range ▸ LinearMap.mem_range_self _ x
  refine ⟨fun g => l ((M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real x g), fun e => hl (congrFun e g₀), fun κ h g => ?_, fun κ hJ g => ?_⟩
  · have e := congrFun (hm.2 ⟨κ, h⟩) g
    exact (congrArg l e).trans (map_smul l _ _)
  · have e1 := ad.read _ hμ k x (g * κ)
    have e2 := ad.read _ hμ k x g
    have e3 := (Y.IL.jMt _ hμ k x).2.2 _ hJ ((ad.PV k).ψ g)
    rw [← map_mul] at e3
    have e4 := e1.trans (e3.trans (congrArg _ e2.symm))
    rw [← map_smul] at e4
    exact (congrArg l ((ad.eW _ hμ k).injective e4)).trans (map_smul l _ _)

set_option maxHeartbeats 1000000 in

theorem types_of (ad : MtAd Y M) {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) {μ0 : T} (hlev : R.toRealDat.toLevCh.Is μ0) (hgl : R.toRealDat.grp_levels F.lv2)
    (i : D.nd.Loc) (μ : D.what₂.Tup) (k : Fin D.R.m) (hμ : μ = D.nd.mu i) (hnt : Nontrivial (D.what₂.Mt μ ((k : ℕ) + 1)))
    (s : SplitPlace D.host.E) (φ : Os s →+* kP s.w) (b : GL (Fin D.R.nV) (kP s.w)) (hs : s.w ∈ R.Pg)
    (hw : ∃ kk v, s.w = D.naut.plGw kk v) (hfr : FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) (ad.PV k) (R.βV k) s φ b) :
    ∃ (f : GAf D.host.E D.R.nV → ℂ) (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ)
      (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
      (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
      f ≠ 0 ∧ NG.IsPsi0 s ψ₀ ∧ NG.LevelUni J χ s D.R.r ψ₀ ξ ∧ (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
      ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → ∀ y : GL (Fin D.R.nV) (Os s), IsCompOf s κ y →
        (IsBlockUpperUnipotentMatrix D.R.r (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹) → ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
        (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g) := by
  have hu : Formalism.IndefR.RecTie.Used0 D μ := hμ ▸ Model.used_loc i
  rw [D.nd.mu_w i] at hμ
  subst hμ
  obtain ⟨kk, v, hv⟩ := hw
  obtain ⟨ψ₀, ξ, h1, -, h2⟩ := hin.uni (D.nd.w i) k kk v s hv
  obtain ⟨f, hf, hJ, hL⟩ := exists_fn ad _ hu k hnt
  obtain ⟨c, hc⟩ := hlev.βV k
  rw [one_pow] at hc
  obtain ⟨ψ0, -, hP0, -⟩ := hgl
  refine ⟨f, _, _, ψ₀, ξ, hf, h1, h2, hJ, fun κ hU hT y hy => ?_⟩
  have key := mem_level (GlobalTheory.FrameBlockDiagonal.rankV D k) (ad.std k) hc
    (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT (D.what₂.muTw (D.nd.w i))) (R.toRealDat.levR F.lv2 false))
    (le_of_eq (GlobalTheory.FrameBlockDiagonal.rankV D k))
    (fun g hg => by
      show g ∈ (R.toRealDat.levR F.lv2 false).H
      rw [hP0]
      exact fun PP _ => hg PP)
    s (fun PP hPP => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hlev _ hPP (Or.inl hs)) hfr hU hT hy
  refine ⟨fun hb => ⟨_, hL κ (key.1 hb)⟩, fun h1 g => ?_⟩
  rw [hL κ (key.2 h1).1 g, (key.2 h1).2, one_mul]

end Read

set_option maxHeartbeats 1000000 in

theorem main : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        ∃ (f : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV → ℂ) (J : Subgroup (Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV)) (χ : J →* ℂˣ)
          (ψ₀ : AddChar (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E)) ℂ)
          (ξ : (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E))ˣ →* ℂˣ),
          f ≠ 0 ∧ Formalism.L2.NG.IsPsi0 s' ψ₀ ∧ Formalism.L2.NG.LevelUni J χ s' (w.st Z).toD7.R.r ψ₀ ξ ∧
          (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
          (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV, ReciprocityTheory.Aut.TrivOutside {s'.v} κ → ∀ y : GL (Fin (w.st Z).toD7.R.nV) (GlobalTheory.CenFrame.Os s'),
        GlobalTheory.CenFrame.IsCompOf s' κ y →
      ((∀ i j : Fin (w.st Z).toD7.R.nV, ((w.st Z).toD7.R.r ≤ i.val → j.val < (w.st Z).toD7.R.r → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → j.val < i.val → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → i = j → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 1)) →
        ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
      (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g)) := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro ad i s k hs hnt s' φ b hPg _ hfr
  obtain ⟨tup, Q, hin⟩ := mtInput_of c.a.nt c.a.all.gal.mt c.a.mt_eq
  obtain ⟨plg, iso, h1, -⟩ := t.r.z.pins.keep.grp
  exact types_of (D := (w.st Z).toD7) ad hin t.r.z.pins.char.base.lev t.r.z.pins.char.base.grp.levels i _ k hs hnt s' φ b hPg
    ⟨(plg.symm ⟨s'.w, hPg⟩).1, (plg.symm ⟨s'.w, hPg⟩).2, by rw [← h1, plg.apply_symm_apply]⟩ hfr

end GlobalTheory.FrameTypes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralRationalAtMemberStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_rational_at_member : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG := by
  first | exact @GlobalTheory.CenRatAt.cenRat_at | exact GlobalTheory.CenRatAt.cenRat_at | (intros; apply GlobalTheory.CenRatAt.cenRat_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

noncomputable section
namespace GlobalTheory.ChernPull

open ReciprocityTheory.L2DbarEstimates (V)
open ComplexConjugate

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem conn_eq_sum (H : V n → Matrix r r ℂ) (z ζ : V n) :
    conn H z ζ = ∑ c, ζ c • conn H z (coordVec c) := by
  have hζ : ζ = ∑ c, ζ c • coordVec (n := n) c := by
    ext i; simp [coordVec, Pi.single_apply]
  conv_lhs => rw [hζ]
  have hl : ∀ (s : Finset (Fin n)), mdel H z (∑ c ∈ s, ζ c • coordVec c) = ∑ c ∈ s, ζ c • mdel H z (coordVec c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext a b; simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mdel_add_vec, mdel_smul_vec, ih]
  simp only [conn, hl, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_sum, Matrix.mul_smul]

theorem curv_eq_sum (H : V n → Matrix r r ℂ) (z ξ ζ : V n) :
    curv H z ξ ζ = ∑ d, conj (ζ d) • curv H z ξ (coordVec d) := by
  have hζ : ζ = ∑ d, ζ d • coordVec (n := n) d := by
    ext i; simp [coordVec, Pi.single_apply]
  conv_lhs => rw [hζ]
  have hl : ∀ (s : Finset (Fin n)), mdbar (fun x => conn H x ξ) z (∑ d ∈ s, ζ d • coordVec d) =
      ∑ d ∈ s, conj (ζ d) • mdbar (fun x => conn H x ξ) z (coordVec d) := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext a b; simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mdbar_add_vec, mdbar_smul_vec, ih]
  simp only [curv, hl, Finset.sum_neg_distrib, smul_neg]

theorem mContDiffAt_conn {H : V n → Matrix r r ℂ} {y : V n} (h2 : MContDiffAt 2 H y)
    (hu : IsUnit (H y).det) (ξ : V n) : MContDiffAt 1 (fun x => conn H x ξ) y := by
  have h1 : MContDiffAt 1 H y := h2.of_le (by norm_num)
  have hu' : IsUnit ((H y)ᵀ).det := by rwa [Matrix.det_transpose]
  exact (h1.transpose.inv hu').mul ((h2.mdel (j := 1) (by norm_num) ξ).transpose)

theorem conn_comp_eventually {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (ξ : V n) :
    ∀ᶠ w in 𝓝 v, conn (fun x => H (φ x)) w ξ = ∑ c, (fderiv ℂ φ w ξ) c • conn H (φ w) (coordVec c) := by
  have hK : ∀ᶠ w in 𝓝 v, MContDiffAt 2 H (φ w) := hφ.continuousAt.eventually h2.eventually_two
  filter_upwards [hK, hφ.eventually_analyticAt] with w hw ha
  rw [← conn_eq_sum]
  have hm : mdel (fun x => H (φ x)) w ξ = mdel H (φ w) (fderiv ℂ φ w ξ) := by
    ext a b
    exact del_comp_holo (u := fun y => H y a b) ((hw a b).differentiableAt (by norm_num))
      ha.differentiableAt ξ
  simp only [conn, hm]

theorem curv_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (ξ η : V n) :
    curv (fun x => H (φ x)) v ξ η = ∑ c, (fderiv ℂ φ v ξ) c • curv H (φ v) (coordVec c) (fderiv ℂ φ v η) := by
  rw [curv, mdbar_congr (conn_comp_eventually hφ h2 ξ)]
  have hd : DifferentiableAt ℂ φ v := hφ.differentiableAt
  have hf : ∀ c : Fin n, DifferentiableAt ℂ (fun x => (fderiv ℂ φ x ξ) c) v := by
    intro c
    have h1 : DifferentiableAt ℂ (fun x => fderiv ℂ φ x ξ) v :=
      hφ.fderiv.differentiableAt.clm_apply (differentiableAt_const ξ)
    exact (EuclideanSpace.proj (𝕜 := ℂ) c).differentiableAt.comp v h1
  have hc : ∀ (c : Fin n) (i j : r), DifferentiableAt ℝ (fun y => conn H y (coordVec c) i j) (φ v) :=
    fun c i j => (mContDiffAt_conn h2 hu (coordVec c)).diff i j
  ext i j
  simp only [Matrix.neg_apply, mdbar_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_neg_distrib]
  rw [dbar_sum (A := fun c x => (fderiv ℂ φ x ξ) c * conn H (φ x) (coordVec c) i j) (fun c _ => ((hf c).restrictScalars ℝ).mul
    ((hc c i j).comp v (hd.restrictScalars ℝ)))]
  rw [ContinuousLinearMap.sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dbar_mul (a := fun x => (fderiv ℂ φ x ξ) c) (b := fun x => conn H (φ x) (coordVec c) i j) ((hf c).restrictScalars ℝ) ((hc c i j).comp v (hd.restrictScalars ℝ)),
    dbar_eq_zero (hf c), dbar_comp_holo (u := fun y => conn H y (coordVec c) i j) (hc c i j) hd]
  simp [curv]

def substAlg (J : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  aeval fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)

def jac (φ : V n → V n) (v : V n) : Matrix (Fin n) (Fin n) ℂ := fun c a => (fderiv ℂ φ v (coordVec a)) c

theorem curv_comp_coord {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (a b : Fin n) :
    curv (fun x => H (φ x)) v (coordVec a) (coordVec b) =
      ∑ c, ∑ d, (jac φ v c a * conj (jac φ v d b)) • curv H (φ v) (coordVec c) (coordVec d) := by
  rw [curv_comp hφ h2 hu]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [curv_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_smul]; rfl

theorem curvPoly_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) :
    curvPoly (fun x => H (φ x)) v = (curvPoly H (φ v)).map (substAlg (jac φ v)) := by
  refine Matrix.ext fun i j => ?_
  simp only [curvPoly, Matrix.of_apply, Matrix.map_apply, curv_comp_coord hφ h2 hu, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, substAlg, aeval_X, aeval_C, algebraMap_eq,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [← Fintype.sum_prod_type']
  let e : Fin n × Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n × Fin n :=
    ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun _ => rfl, fun _ => rfl⟩
  exact Fintype.sum_equiv e _ _ fun x => by simp only [e, Equiv.coe_fn_mk]; ring

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {d : Type} [Fintype d]
    [DecidableEq d] (M : Matrix d d A) :
    (Matrix.charpolyRev M).map f = Matrix.charpolyRev (M.map f) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 1
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem chernPoly_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (k : ℕ) :
    chernPoly (fun x => H (φ x)) v k = substAlg (jac φ v) (chernPoly H (φ v) k) := by
  unfold chernPoly
  rw [curvPoly_comp hφ h2 hu]
  have hm : -(curvPoly H (φ v)).map (substAlg (jac φ v)) = (-curvPoly H (φ v)).map (substAlg (jac φ v)).toRingHom := by
    rw [Matrix.map_neg (f := (substAlg (jac φ v)).toRingHom) (fun a => map_neg _ a)]; rfl
  rw [hm, ← charpolyRev_map, Polynomial.coeff_map]
  rfl

theorem jac_eq_toMatrix (φ : V n → V n) (v : V n) :
    jac φ v = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (fderiv ℂ φ v : V n →ₗ[ℂ] V n) := by
  ext c a
  simp [LinearMap.toMatrix_apply, jac, coordVec]

end GlobalTheory.ChernPull

open ReciprocityTheory.L2DbarEstimates (V) in

theorem GlobalTheory.ChernPull.chernTop_comp : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (K : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n) (v : ReciprocityTheory.L2DbarEstimates.V n), AnalyticAt ℂ φ v → (∀ τ, MContDiffAt 2 (fun u => K u τ) (φ v)) → (∀ τ, IsUnit (K (φ v) τ).det) → chernTop R (fun w => K (φ w)) v = Complex.normSq (LinearMap.det (fderiv ℂ φ v : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n)) * chernTop R K (φ v) := by
  intro n ι m R K φ v hφ h2 hu
  unfold chernTop
  have hc : ∀ x : ι × ℕ, chernPoly (fun u => K (φ u) x.1) v x.2 =
      GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v) (chernPoly (fun u => K u x.1) (φ v) x.2) :=
    fun x => GlobalTheory.ChernPull.chernPoly_comp hφ (h2 x.1) (hu x.1) x.2
  simp only [hc]
  have ha := congrArg (fun F => F R) (MvPolynomial.comp_aeval (R := ℝ)
    (f := fun x : ι × ℕ => chernPoly (fun u => K u x.1) (φ v) x.2)
    ((GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v)).restrictScalars ℝ))
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at ha
  rw [← ha, GlobalTheory.ChernPull.substAlg, GlobalTheory.T.topDegreeFormCoeff_linearSubst_eq_absDet_sq_mul, Complex.mul_conj, GlobalTheory.ChernPull.jac_eq_toMatrix,
    LinearMap.det_toMatrix, Complex.re_ofReal_mul]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldEqLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_field_eq_level : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ _ => t.r.z.R.C = TC.cf w.I w.l Z := by
  first | exact @GlobalTheory.HeightCounting.Up.CoefficientAgreement.tied_cf | exact GlobalTheory.HeightCounting.Up.CoefficientAgreement.tied_cf | (intros; apply GlobalTheory.HeightCounting.Up.CoefficientAgreement.tied_cf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricGramSmoothInFamilyFramesStatement
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenMetricGram_smooth_in_familyFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ A ∈ S.S (under y), ∀ (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).re) y ∧ CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).im) y := by
  first | exact @GlobalTheory.LieBase.cInfAt_gramOf | exact GlobalTheory.LieBase.cInfAt_gramOf | (intros; apply GlobalTheory.LieBase.cInfAt_gramOf <;> assumption)
end

