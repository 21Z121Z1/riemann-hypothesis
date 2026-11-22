import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0464
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0449
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0007
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0002
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0007
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0004
import Formalism.LocalToGlobal.JointCharacters.SameChr
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TilX Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopPtModel

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_mul {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (a b : GL (Fin N) (AfE F E)) :
    ((a * b : GL (Fin N) (AfE F E)).1).map (adAt F P) = a.1.map (adAt F P) * b.1.map (adAt F P) := by
  rw [Units.val_mul, Matrix.map_mul]

theorem adAt_inv_one {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) {a : GL (Fin N) (AfE F E)} (h : a.1.map (adAt F P) = 1) :
    ((a⁻¹ : GL (Fin N) (AfE F E)).1).map (adAt F P) = 1 := by
  have := adAt_mul P a a⁻¹
  rw [mul_inv_cancel, h, one_mul, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this.symm

theorem adAt_of_prV {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) {k : GL (Fin N) (AfE F E)}
    (h1 : bc (prV (E := E) (P.under (𝓞 F))) k = 1) : k.1.map (adAt F P) = 1 := by
  refine Matrix.ext fun i j => ?_
  have h2 : prV (E := E) (P.under (𝓞 F)) (k.1 i j - (1 : Matrix (Fin N) (Fin N) (AfE F E)) i j) = 0 := by
    have h3 := congrArg (fun g : GL (Fin N) _ => g.1 i j) h1
    simp only [Units.val_one] at h3
    have h4 : prV (E := E) (P.under (𝓞 F)) (k.1 i j) = (1 : Matrix (Fin N) (Fin N) _) i j := h3
    rw [map_sub, h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 := adAt_eq_zero_of_prV P _ h2
  rw [map_sub, sub_eq_zero] at h3
  refine h3.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem prV_of_adAt {N : ℕ} (v : HeightOneSpectrum (𝓞 F)) {k : GL (Fin N) (AfE F E)}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → k.1.map (adAt F w) = 1) : bc (prV (E := E) v) k = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show prV (E := E) v (k.1 i j) = (1 : Matrix (Fin N) (Fin N) _) i j
  have h2 : prV (E := E) v (k.1 i j - (1 : Matrix (Fin N) (Fin N) (AfE F E)) i j) = 0 := by
    refine (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v _).1.2 fun w hw => ?_
    have h3 : adAt F w (k.1 i j) = (1 : Matrix (Fin N) (Fin N) _) i j := congrFun (congrFun (h w hw) i) j
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [map_sub, sub_eq_zero] at h2
  refine h2.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

theorem topPt_base {u : B.Word} {a : I.ι} {k : GA B (B.R.N B.R.m)} [NeZero (B.R.N B.R.m - 1)] (h : I.TopPt l Z u a k) :
    PtOf k (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u (DecoF.base _ _ _ _ _)) := by
  have := h (DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _) ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rwa [one_mul] at this

theorem topPt_last (hI : I.Ok) {u : B.Word} {a : I.ι} {k : GA B (B.R.N B.R.m)} [NeZero (B.R.N B.R.m - 1)] (h : I.TopPt l Z u a k)
    (P : I.Q a) (i : Fin (B.R.N B.R.m)) : adAt B.host.F P.1 (k.1 i (Br.iL (N_m_succ B.R))) =
      algebraMap B.host.E _ ((Pi.single (Br.iL (N_m_succ B.R)) ((X.piT u : 𝓞 B.host.E) : B.host.E) : Fin _ → B.host.E) i) := by
  have hPr := (base_fields_primes_ok B X).2.1
  have h1 := (topPt_base I l Z h).fr P i (Br.iL (N_m_succ B.R))
  have h2 := tilFr_fr_last (N_m_succ B.R) (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u)
    (fun P : I.Q a => ((TwistPrimes.twist_primes_away I hI).2 u a P.1 P.2).2.1) (DecoF.base _ _ _ _ _) P
  exact h1.trans (congrArg (fun x => algebraMap B.host.E _ (x i)) h2)

theorem exists_topPt (hI : I.Ok) (hP : TC.Pins B X) (u : B.Word) (a : I.ι) : ∃ k : GA B (B.R.N B.R.m),
    (∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m)) ∧
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v → bc (prV (E := B.host.E) v) k = 1) ∧
    (∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = B.R.N B.R.m →
      HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j))
        (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) ∧
    I.TopPt l Z u a k := by
  have hX := (base_fields_primes_ok B X).1
  have hPr := (base_fields_primes_ok B X).2.1
  haveI : NeZero (B.R.N B.R.m) := ⟨by have := N_m_succ B.R; omega⟩
  have hq := (TwistPrimes.twist_primes_away I hI).2 u a
  obtain ⟨k, h1, h2, h3⟩ := BasePoint.exists_kStd X hPr u (B.R.N B.R.m)
  obtain ⟨t, t1, t2, t3⟩ := TwUnit.exists_tw B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a)
    (fun P hP => (hq P hP).1) (X.piT u) (fun P hP => (hq P hP).2.1)
  have t4 : ∀ w, w ∉ I.Q a → conjPrime₂ w ∉ I.Q a → t.1.map (adAt B.host.F w) = 1 := fun w a1 a2 => by
    refine Matrix.ext fun i j => ?_
    exact (t3 w a1 a2 i j).trans Matrix.one_apply.symm
  have hcc : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), conjPrime₂ (conjPrime₂ P) = P := fun P => by
    ext x
    rw [mem_conjP, mem_conjP, cO_cO]
  have hun : ∀ Q : HeightOneSpectrum (𝓞 B.fields.E), (conjPrime₂ Q).under (𝓞 B.fields.F) = Q.under (𝓞 B.fields.F) := fun Q => by
    ext r
    have e : cO B.fields.E (algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E) r) = algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E) r :=
      RingOfIntegers.ext (hX.star_F (r : B.fields.F))
    show algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E) r ∈ (conjPrime₂ Q).asIdeal ↔ algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E) r ∈ Q.asIdeal
    rw [mem_conjP, e]
  refine ⟨k * t, TopCh.KStd.exists_ptOf_mul_K1 _ _ _ k t t1 h1, fun v hv hu => ?_, fun P r j hr => ?_,
    TilQ.pt_tilF_gen I hI hP l Z u a k t h1 h2 h3 t1 t2⟩
  · rw [map_mul, h2 v hv, one_mul]
    exact prV_of_adAt v fun w hw => t4 w (fun h => hu ⟨w, h, hw⟩) (fun h => hu ⟨_, h, (hun w).trans hw⟩)
  · have e1 := adAt_inv_one P.1 (t4 P.1 (fun h => (hq _ h).1.1 P.2) (fun h => (hq _ h).1.2.2.1 ((hcc P.1).symm ▸ P.2)))
    have e2 := adAt_mul (F := B.host.F) (E := B.host.E) P.1 t⁻¹ k⁻¹
    rw [e1, one_mul, ← _root_.mul_inv_rev] at e2
    have e3 : adAt B.host.F P.1 (((k * t)⁻¹ : GA B (B.R.N B.R.m)).1 r j) = adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j) :=
      congrFun (congrFun e2 r) j
    exact e3 ▸ h3 P r j hr

theorem not_topPt_one (hI : I.Ok) {u : B.Word} {a : I.ι} [NeZero (B.R.N B.R.m - 1)] (P : I.Q a)
    (hpi : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 1) : ¬ I.TopPt l Z u a 1 := fun h => by
  have h1 := topPt_last I l Z hI h P (Br.iL (N_m_succ B.R))
  rw [Pi.single_eq_same, Units.val_one, Matrix.one_apply_eq, map_one] at h1
  exact hpi ((algebraMap B.host.E _).injective (h1.symm.trans (map_one _).symm))

end GlobalTheory.Mem.Col2.TopPtModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.factResChar

inductive IsRecG (sc : Scale) (D : D7) (Gt : GatTies D) (c : LatCmp D) (H : Formalism.L2.Herm.Herm0 D) (F : ∀ u, Forms0 D u) : Prop
  | intro
    (D0 : D7)
    (Lc : ∀ u, ColLevel D0.R D0.host.F D0.host.E D0.sp D0.host.g (D0.mem u).C (D0.mem u).A (D0.clsLat u))
    (I : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      LocId (Lc u) (D0.what₂.places.resChar w) (nOrb (zH D0.R.toFrame (hP D0 (D0.what₂.places.resChar w))))
      (WQ (D0.what₂.places.resChar w) (nFr D0 (D0.what₂.places.resChar w)))
      (QQ (D0.what₂.places.resChar w) (nFr D0 (D0.what₂.places.resChar w))))
    (ψ : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D0.what₂.places.resChar w) →* (ORec D0 w (nFr D0 (D0.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D0 Lc I ψ u w h).gat (rSc sc D0.R.k (D0.what₂.places.resChar w))
      (epSc D0.R sc 1 (D0.what₂.places.resChar w))).d = Module.finrank ℂ (D0.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D0 sc 1 Lc I ψ hd))
    (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D0.what₂.Word, Forms0 (recC D0 sc 1 Lc I ψ hd) u)
    (B : GL (Fin D0.R.k) D0.host.E)
    (hBs : Cmp.StdB (recC D0 sc 1 Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D0.host.F)) (h : ((D0.what₂.places.resChar w : ℕ) : 𝓞 D0.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
      (inclE (F := D0.host.F) (w'.adicCompletion D0.host.F))) B)
    (iK : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      KfRec D0 w (nFr D0 (D0.what₂.places.resChar w)) →+* ℂ_[D0.what₂.places.resChar w])
    (lam : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D0.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D0.what₂.LL), iK u w hg (embRec D0 w (nFr D0 (D0.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D0.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D0 Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (CH : CmpHyp0P T (gatTiesC D0 sc 1 Lc I ψ hd) (cmpInC D0 sc 1 Lc I ψ hd H0 hL B hBs hB))
    (eq : (⟨D, Gt, c, H, F⟩ : Σ D : D7, GatTies D × LatCmp D × Formalism.L2.Herm.Herm0 D × ∀ u, Forms0 D u) =
      ⟨recC D0 sc 1 Lc I ψ hd, gatTiesC D0 sc 1 Lc I ψ hd,
      Cmp.latCmpC T (gatTiesC D0 sc 1 Lc I ψ hd) (cmpInC D0 sc 1 Lc I ψ hd H0 hL B hBs hB)
        (CH.toHyp0 fun u w hg v s x => pos_C D0 sc 1 Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x).toHyp, H0, T⟩)
    : IsRecG sc D Gt c H F

end Rec

def Half (B : Base) (Pv : HeightOneSpectrum (𝓞 B.host.F) → HeightOneSpectrum (𝓞 B.host.E)) : Prop :=
  ∀ v v' (p : ℕ), p.Prime → (p : 𝓞 B.host.F) ∈ v.asIdeal → (p : 𝓞 B.host.F) ∈ v'.asIdeal →
    (Pv v).under (𝓞 B.host.K) = (Pv v').under (𝓞 B.host.K)

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure ColPin (w : ColW B f T) : Type where
  isTw : TC.IsTw w.I
  jets : ColIn.JetsIn w.I
  hX : B.fields.Ok
  above : ∀ v, w.I.sel v ∈ aboveF (L := B.host.E) B.host.F v
  half : Half B w.I.sel
  d3b : PlacesOverCommonPrime B.host
  selectedPlacesAgree : (∀ v hv, w.I.sel v = d3b.P v hv) ∧ ∀ v hv, w.I.sel v = d3b.P' v hv
  vals : ∀ a P, (w.I.xi a).UnrAt P → ∃ z : B.LL, B.embLL z = (((w.I.xi a).val P : ℂˣ) : ℂ)
  roots : ∀ a, ∀ P ∈ w.I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal))

def Pinned : WP := fun _ _ _ _ w => Nonempty (ColPin w)

structure ColumnDataSplitPrimes (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 extends ColT w Z where
  isRec : IsRecG K.s (w.D Z) Gt cmp g.herm g.forms
  om : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (w.D Z) w.I.J.δ

def GIs2 (K : Ctx) (w : ColW B f T) (G : GJStage B w.C) : Prop :=
  ∀ W V S N, Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, G⟩) ∧ GatNum K.s (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩)

structure NchT (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) : Type where
  tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch
  xi : tp.xi = w.I.xi
  psi : tp.psi = T.psi
  tie : NChTie (w.D Z) nch
  Q : ∀ v ∈ Wt, nch.Q v = T.Q v ∧ nch.k' v = T.k v
  chrPsi : PsiChoiceCompatible (w.D Z) (TC.cf w.I w.l Z) nch tp

abbrev KerFam (D : D7) (Gt : GatTies D) (cmp : LatCmp D) (tw : TwForms D) (Gy : G.LatInst D) : Type _ :=
  ∀ u v (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)),
    haveI : Fact (D.what₂.places.resChar v).Prime := ⟨D.what₂.places.resChar_prime v⟩
    LocalToGlobal₂ D Gt cmp tw u v h (Gy.Ch u v h)

structure KerT {w : ColW B f T} {Z : w.Lt} (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z))
    (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) : Type 1 where
  O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)
  std : TC.StdO w.I w.l Z Y.Qp O
  unf : ∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i
  E : KerEnt (w.D Z) Y (w.tw Z)
  ok : TC.EntOk E O
  lam : ∀ u v h, haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
    (ker u v h).lam = E.lam v
  served : ∀ u v h, haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
    ThAtServed (ker u v h) E
  iw : ∀ u v h, haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
    Formalism.L2.Herm.SymmetricKernelCompatibleAtPlace t.full.1.base.toHermColsCh t.full.1.g u v h (ker u v h)
  iw_pos : ∀ u v h, haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
    Formalism.L2.Herm.GIwPos u v h (ker u v h)

structure DivT {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (Y : DivX (w.D Z)) :
    Type 1 where
  Qp : TC.QpIs w.I Y.Qp
  chr : DivisorCharacterCompatibility (w.D Z) (TC.cf w.I w.l Z) nch n.tp Y
  loc : Formalism.L2.DIV.QLocTiedC chr w.I.sel
  inK : Y.Lev → ℕ → Prop
  geo : Formalism.L2.Geo.GeoTiedP Y inK

structure ThT {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (th : ThetaX (w.D Z)) :
    Type 1 where
  provA : TH.ProvA
  all : Formalism.L2.Theta.AllTied (w.D Z) th provA
  weq : Formalism.L2.Theta.WeilCompatibleEquivariance all.W
  chr : ThetaChrTied (w.D Z) (TC.cf w.I w.l Z) nch n.tp th
  same : Formalism.L2.JoinChr.SameChr all.T chr
  std : Formalism.L2.Theta.IsStdChar (w.D Z) all.W.ψ (-1)
  io : th.TieIo

def RetwistW (p : WP) (P P' : CP) : Prop :=
  Pass KPx (positionOf P) fun K B f T => ∃ w : ColW B f T, p K B f T w ∧ ∀ (Z : w.Lt) (c : V4.Core K (w.st Z) f T), P K B f T w Z c →
    DQ.TwAllAt (w.D Z) c.O.nch c.O.xd ∧ P' K B f T w Z c

theorem GIs2.gIs {w : ColW B f T} {G : GJStage B w.C} (h : GIs2 K w G) : GIs K w G := fun W V S N =>
  let ⟨a, b, ⟨t⟩⟩ := h W V S N; ⟨a, b, ⟨t.toColT⟩⟩

end GlobalTheory.Mem.Top.Bl

end
end

