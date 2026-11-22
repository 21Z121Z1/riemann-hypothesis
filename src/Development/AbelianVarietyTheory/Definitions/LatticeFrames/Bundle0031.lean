import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Formalism.LocalRingCardinality.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

section Coord

variable {K : Type} [Field K] {Y : Type} [Fintype Y] [DecidableEq Y] (V : HSp D) (pr : AE D →+* K)
  (β : Matrix (Fin V.rank) Y K) (γ : Matrix Y (Fin V.rank) K) (βγ : β * γ = 1) (γβ : γ * β = 1)

def coordHom (βγ : β * γ = 1) (γβ : γ * β = 1) : GA D V →* GL Y K :=
  MonoidHom.toHomUnits
    { toFun := fun κ => γ * (mt V κ).map pr * β
      map_one' := by simp [Formalism.L2.Theta.mt, γβ]
      map_mul' := fun κ κ' => by
        have h : (mt V (κ * κ')).map pr = (mt V κ).map pr * (β * γ) * (mt V κ').map pr := by
          rw [βγ, Matrix.mul_one, ← Matrix.map_mul]; simp [Formalism.L2.Theta.mt]
        rw [h]; simp only [Matrix.mul_assoc] }

theorem coordHom_val (κ : GA D V) : (coordHom V pr β γ βγ γβ κ).val = γ * (mt V κ).map pr * β := rfl

theorem eq_coordHom_iff (κ : GA D V) (g : GL Y K) :
    (mt V κ).map pr = β * g.val * γ ↔ g = coordHom V pr β γ βγ γβ κ := by
  constructor
  · intro h
    refine Units.ext ?_
    rw [coordHom_val, h]
    calc g.val = (γ * β) * g.val * (γ * β) := by simp [γβ]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rintro rfl
    rw [coordHom_val]
    calc (mt V κ).map pr = (β * γ) * (mt V κ).map pr * (β * γ) := by simp [βγ]
      _ = _ := by simp only [Matrix.mul_assoc]

def movesGrp (L : GlobalTheory.FinPl.Lat V) (P : GlobalTheory.FinPl.Pl D → Prop) : Subgroup (GA D V) where
  carrier := {κ | GlobalTheory.FinPl.Moves V κ L L P}
  one_mem' := fun y _ => by simp [Formalism.L2.Theta.mt]
  mul_mem' := fun {κ κ'} h h' y hy => by
    have hy' : ∀ i, (mt V κ' *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D P := fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
    rw [h' y hy, h _ hy', Matrix.mulVec_mulVec]
    simp [Formalism.L2.Theta.mt]
  inv_mem' := fun {κ} h y hy => by
    have hy' : ∀ i, (mt V κ⁻¹ *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D P := fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
    rw [h _ hy', Matrix.mulVec_mulVec]
    have : mt V κ * mt V κ⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt]; rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [this, Matrix.one_mulVec]

end Coord

section AtLevel

variable {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP)

def GX.MatAt {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP) (κ : GA D (D.sp.X 0))
    (g : GL (XIx (Fin D.R.k) (Fin D.R.t) 0) H.k) : Prop :=
  (mt (D.sp.X 0) κ).map H.q.pr = (H.FX 0 (Nat.zero_le _)).β * g.val * (H.FX 0 (Nat.zero_le _)).γ

abbrev GX.lev0 {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP) :=
  (H.S.T (Fin D.R.t)).lev 0 (H.s + 1) (Nat.zero_add _)

def GX.mat0 : GA D (D.sp.X 0) →* GL (XIx (Fin D.R.k) (Fin D.R.t) 0) H.k :=
  coordHom (D.sp.X 0) H.q.pr _ _ (H.FX 0 (Nat.zero_le _)).βγ (H.FX 0 (Nat.zero_le _)).γβ

theorem GX.matAt_iff (κ : GA D (D.sp.X 0)) (g : GL (XIx (Fin D.R.k) (Fin D.R.t) 0) H.k) : H.MatAt κ g ↔ g = H.mat0 κ :=
  eq_coordHom_iff _ _ _ _ _ _ κ g

end AtLevel

def OffX.mat0 (i : ι) : GA D (D.sp.X 0) →* GL (Fin (D.sp.X 0).rank) k :=
  coordHom (D.sp.X 0) (o.p i).pr _ _ (o.β 0 i).bb' (o.β 0 i).b'b

def InLev0 (κ : GA D (D.sp.X 0)) : Prop :=
  GlobalTheory.FinPl.Moves (D.sp.X 0) κ (a.x 0).L (a.x 0).L (fun _ => True) ∧
    (∀ i (g : GL (Fin (D.sp.X 0).rank) k), (mt (D.sp.X 0) κ).map (o.p i).pr = (o.β 0 i).b * g.val * (o.β 0 i).b' →
      g • o.Q 0 i = o.Q 0 i) ∧
    ∀ PP g, (G PP).MatAt κ g → embX ((G PP).s + 1) g ∈ (G PP).lev0.J

theorem inLev0_iff (κ : GA D (D.sp.X 0)) : InLev0 o G κ ↔
    GlobalTheory.FinPl.Moves (D.sp.X 0) κ (a.x 0).L (a.x 0).L (fun _ => True) ∧ (∀ i, o.mat0 i κ • o.Q 0 i = o.Q 0 i) ∧
      ∀ PP, embX ((G PP).s + 1) ((G PP).mat0 κ) ∈ (G PP).lev0.J := by
  refine and_congr Iff.rfl (and_congr (forall_congr' fun i => ?_) (forall_congr' fun PP => ?_))
  · simp only [eq_coordHom_iff _ _ _ _ (o.β 0 i).bb' (o.β 0 i).b'b, forall_eq]
    rfl
  · simp only [GX.matAt_iff, forall_eq]

def levelZeroSubgroup : Subgroup (GA D (D.sp.X 0)) :=
  movesGrp (D.sp.X 0) (a.x 0).L (fun _ => True) ⊓
    ((⨅ i, (MulAction.stabilizer (GL (Fin (D.sp.X 0).rank) k) (o.Q 0 i)).comap (o.mat0 i)) ⊓
      ⨅ PP, ((G PP).lev0.J.comap (embX ((G PP).s + 1))).comap (G PP).mat0)

theorem mem_lev0Grp (κ : GA D (D.sp.X 0)) : κ ∈ levelZeroSubgroup o G ↔ InLev0 o G κ := by
  rw [inLev0_iff]
  simp only [levelZeroSubgroup, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  rfl

variable {o G} in

theorem InLev0.mul {κ κ' : GA D (D.sp.X 0)} (h : InLev0 o G κ) (h' : InLev0 o G κ') : InLev0 o G (κ * κ') :=
  (mem_lev0Grp o G _).1 (mul_mem ((mem_lev0Grp o G _).2 h) ((mem_lev0Grp o G _).2 h'))

variable {o G} in

theorem InLev0.inv {κ : GA D (D.sp.X 0)} (h : InLev0 o G κ) : InLev0 o G κ⁻¹ :=
  (mem_lev0Grp o G _).1 (inv_mem ((mem_lev0Grp o G _).2 h))

open scoped Pointwise in
variable {o G} in

theorem InLev0.smul_ker {κ : GA D (D.sp.X 0)} (h : InLev0 o G κ) (i : ι) : o.mat0 i κ • (o.Q 0 i).ker = (o.Q 0 i).ker := by
  rw [← Pair.smul_ker, ((inLev0_iff o G κ).1 h).2.1 i]

structure Arith : Prop where
  unifT : ∀ i, valuation k ((o.p i).pr (incA D (((D.mem u).A.T : ℕ) : D.host.E))) = valuation k ((o.q.1 : 𝒪[k]) : k)
  oneG : ∀ PP, valuation (G PP).k ((G PP).q.pr (incA D (((D.mem u).A.T : ℕ) : D.host.E)) - 1) < 1
  unifG : ∀ PP, valuation (G PP).k ((G PP).q.pr (incA D ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))) =
    valuation (G PP).k (((G PP).S.ϖ : (G PP).kˣ) : (G PP).k)
  under : ∀ PP : a.c.Pg, (G PP).q.v = PP.1.under (𝓞 D.host.F)
  tame : ∀ v, GlobalTheory.FinPl.Tame D v
  unr : ∀ v, v ∉ a.c.S → CharUnramAt D a.c.η v ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → CharUnramAt D (a.c.μ j) v
  pos : ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef
  lz : a.Lz.SigOK ∧ a.Lz.IsPosDef

theorem Arith.of_local
    (unifT : ∀ i, valuation k ((o.p i).pr (incA D (((D.mem u).A.T : ℕ) : D.host.E))) = valuation k ((o.q.1 : 𝒪[k]) : k))
    (oneG : ∀ PP, valuation (G PP).k ((G PP).q.pr (incA D (((D.mem u).A.T : ℕ) : D.host.E)) - 1) < 1)
    (unifG : ∀ PP, valuation (G PP).k ((G PP).q.pr (incA D ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))) =
      valuation (G PP).k (((G PP).S.ϖ : (G PP).kˣ) : (G PP).k))
    (under : ∀ PP : a.c.Pg, (G PP).q.v = PP.1.under (𝓞 D.host.F))
    (unr : ∀ v, v ∉ a.c.S → CharUnramAt D a.c.η v ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → CharUnramAt D (a.c.μ j) v)
    (lz : a.Lz.SigOK ∧ a.Lz.IsPosDef) : Arith o G :=
  ⟨unifT, oneG, unifG, under, GlobalTheory.FinPl.TamePlaces.tame D, unr, D.X_posDef, lz⟩

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.FamAllQ
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

def qPrime (W : RealPack ex) (t : W.P.T) (p : ℕ) : Prop := ∃ PP ∈ (pk W).Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal

def RatioQ {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u) : Prop :=
  ∀ n, 2 * n = D.R.m → ∀ t, (f.t t).cTop n ≠ 0 ∧ UnitRatio (qPrime W t) ((f.t t).cTop n / (f.t t).cBot)
    ((f.t W.P.A3.A.μ0).cTop n / (f.t W.P.A3.A.μ0).cBot)

def ServedQ (W : RealPack ex) : Prop :=
  ∀ w (p : ℕ), p.Prime → qPrime W (W.Q.Rl.mu w) p → (p : 𝓞 D.what₂.LL) ∉ w.asIdeal

def FamAllQ (W : RealPack ex) : Prop :=
  ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u, ∃ (f : FamCh W u) (d : BotDat W u),
    d.Pin z ∧ LawsX f.t ∧ LinkZero f d ∧ LinkTail f ∧ LinkDown f ∧ LinkOnto f ∧ LinkComm f ∧ RatioQ f

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.FinAfLocalIdele
section
noncomputable section

namespace GlobalTheory.Core.Cls.JointsStd

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.L2.Host.CT Neutral.B1

section Refl

variable {E : Type} [Field E] [NumberField E]

end Refl

section Std

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_vG_over {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (k : Fin 2) (v : HeightOneSpectrum (𝓞 X.F))
    (h : ((Pr.g k : ℕ) : 𝓞 X.F) ∈ v.asIdeal) : ∃ w ∈ Pr.vG k, w.under (𝓞 X.F) = v := by
  have := v.isPrime
  obtain ⟨⟨w, hwp, hwl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 X.E)) := inferInstance
  have hw : ∀ a : 𝓞 X.F, algebraMap (𝓞 X.F) (𝓞 X.E) a ∈ w ↔ a ∈ v.asIdeal := fun a => by
    rw [hwl.over]; rfl
  have hg0 : ((Pr.g k : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime k).ne_zero
  have hg : ((Pr.g k : ℕ) : 𝓞 X.E) ∈ w := by simpa using (hw _).2 h
  have h0 : X.conjO (Pr.piG k) ≠ 0 := right_ne_zero_of_mul (a := Pr.piG k) (by rw [hPr.piG_norm k]; exact hg0)
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  have hF : ∀ a : 𝓞 X.F, X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) a) = algebraMap (𝓞 X.F) (𝓞 X.E) a := fun a =>
    RingOfIntegers.ext (hX.star_F (a : X.F))
  have hg' := hg
  rw [← hPr.piG_norm k] at hg'
  rcases hwp.mem_or_mem hg' with h1 | h1
  · refine ⟨⟨w.comap X.conjO, Ideal.comap_isPrime _ _, fun e => h0 ?_⟩, (mem_divs h0 _).2 ?_, HeightOneSpectrum.ext (Ideal.ext fun a => ?_)⟩
    · exact Ideal.mem_bot.1 (e ▸ (show X.conjO (X.conjO (Pr.piG k)) ∈ w by rw [hcc]; exact h1))
    · show X.conjO (X.conjO (Pr.piG k)) ∈ w
      rw [hcc]; exact h1
    · show X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) a) ∈ w ↔ _
      rw [hF, hw]
  · exact ⟨⟨w, hwp, fun e => hg0 (Ideal.mem_bot.1 (e ▸ hg))⟩, (mem_divs h0 _).2 h1, HeightOneSpectrum.ext (Ideal.ext hw)⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
include hOk

theorem piBar_std (k : Fin 2) : ∃ y : 𝓞 B.host.K,
    ((y : B.host.K) : B.host.E) = (B.fields.conjO (X.piG k) : B.host.E) ∧ y ∈ (I.C.P.pb k).asIdeal := by
  have hPr := (base_fields_primes_ok B X).2.1
  have hK : (B.fields.conjO (X.piG k) : B.host.E) ∈ B.host.K := by
    have h := HostK.conj_mem B.host (X.piG_K k)
    rw [← B.fields_star] at h
    exact h
  have hi : IsIntegral ℤ (⟨_, hK⟩ : B.host.K) :=
    (isIntegral_algebraMap_iff (algebraMap B.host.K B.host.E).injective).1 (B.fields.conjO (X.piG k)).2
  refine ⟨⟨_, hi⟩, rfl, ?_⟩
  have := (I.C.P.pb k).isPrime
  obtain ⟨⟨w, hwp, hwl⟩⟩ : Nonempty ((I.C.P.pb k).asIdeal.primesOver (𝓞 B.host.E)) := inferInstance
  have hg0 : ((B.host.g k : ℕ) : 𝓞 B.host.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime k).ne_zero
  have hg : ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ w := by
    have h1 := I.C.P.pb_over k
    rw [hwl.over] at h1
    simpa using (Ideal.mem_comap.1 h1)
  have h0 : B.fields.conjO (X.piG k) ≠ 0 := right_ne_zero_of_mul (a := X.piG k) (by rw [hPr.piG_norm k]; exact hg0)
  have h2 := (hOk.pibar k ⟨w, hwp, fun e => hg0 (Ideal.mem_bot.1 (e ▸ hg))⟩).2 (HeightOneSpectrum.ext hwl.over.symm)
  rw [hwl.over]
  exact (mem_divs h0 _).1 h2

theorem om_std (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g) (hG : I.IdG l Z G)
    (k : Fin 2) (v : HeightOneSpectrum (𝓞 B.host.F)) (h : (B.host.g k : 𝓞 B.host.F) ∈ v.asIdeal) (a n : ℕ)
    (hn : n.Coprime (B.host.g k)) (ha : a < B.R.m) :
    G.chiB k v h a (n : kv B.host.F v) = ((I.C.W.om k (ZMod.unitOfCoprime n hn) ^ (2 * (a + 1)) : ℂˣ) : ℂ) := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨w, hw, hv⟩ := exists_vG_over hX hPr k v h
  have hws : w ∈ (B.primes X).vGs := by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hw, Or.inr hw]
  have hg : ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ w.asIdeal := by
    rw [← hv] at h
    simpa using (Ideal.mem_comap.1 h)
  have hu : IsUnit ((n : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) := by
    have h1 : IsCoprime ((n : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) ((B.host.g k : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) := hn.cast
    have h2 : ((B.host.g k : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk w.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hg
    rwa [h2, isCoprime_zero_right] at h1
  have hn0 : ((n : ℕ) : B.host.E) ≠ 0 := by
    rintro e
    obtain rfl : n = 0 := Nat.cast_eq_zero.1 e
    have := w.isPrime
    simp at hu
  have e1 := hG.chi k v h ⟨w, hws⟩ hv ⟨a, ha⟩ n hu.unit rfl
  have e2 := (hOk.ch_tied.mu0 ⟨a, ha⟩).atg ⟨w, hws⟩ (Units.mk0 _ hn0) (n : 𝓞 B.fields.E) hu.unit (by simp) (by simp)
  have e3 := (I.C.isMu0 ⟨a, ha⟩).atg k w ((hOk.pibar k w).1 hw) n hn (Units.mk0 _ hn0) rfl
  rw [e3, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, inv_inj] at e2
  exact e1.trans e2.symm

variable (hP : TC.Pins B X) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L}
  {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}
include hP

end Std

section Local

open Formalism.L2.DIV GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idem_comp {e : AfE F E} {P : HeightOneSpectrum (𝓞 E)} (he : e * e = e)
    (h : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ e * (((x : E)⁻¹) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∉ RInt F E)) :
    afIso F E e P = 1 ∧ ∀ Q, Q ≠ P → afIso F E e Q = 0 := by
  have h01 : ∀ Q, afIso F E e Q = 0 ∨ afIso F E e Q = 1 := fun Q => by
    have h1 : afIso F E e Q * afIso F E e Q = afIso F E e Q := congrArg (fun z => z Q) ((map_mul (afIso F E) e e).symm.trans (congrArg _ he))
    exact IsIdempotentElem.iff_eq_zero_or_one.1 h1
  have hv : ∀ (x : 𝓞 E) Q, afIso F E (e * (((x : E)⁻¹) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))) Q =
      afIso F E e Q * algebraMap E (Q.adicCompletion E) (x : E)⁻¹ := fun x Q => by
    rw [map_mul, afIso_tmul_one]; rfl
  have h0 : ∀ Q, Q ≠ P → afIso F E e Q = 0 := fun Q hQ => by
    refine (h01 Q).resolve_right fun h1 => ?_
    obtain ⟨x, hx, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
      by_contra hc
      push Not at hc
      exact hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hc))
    have hx0 : x ≠ 0 := fun e0 => hxP (e0 ▸ zero_mem _)
    have h2 := (mem_rInt_iff F E _).1 (not_not.1 ((h x hx0).not.1 hxP)) Q
    rw [hv, h1, one_mul, valued_algebraMap, map_inv₀] at h2
    have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) Q x).2 hx
    have h4 : 0 < Q.valuation E (algebraMap (𝓞 E) E x) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx0))
    exact absurd ((inv_le_one₀ h4).1 h2) (not_le.2 h3)
  refine ⟨(h01 P).resolve_left fun h1 => ?_, h0⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  refine (h x hx0).1 hx ((mem_rInt_iff F E _).2 fun Q => ?_)
  rw [hv]
  by_cases hQ : Q = P
  · subst hQ; rw [h1]; simp
  · rw [h0 Q hQ]; simp

theorem finAf_localIdele {e : AfE F E} {P : HeightOneSpectrum (𝓞 E)} (he : e * e = e)
    (h : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ e * (((x : E)⁻¹) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∉ RInt F E)) (k : Eˣ) :
    (finAf F E (localIdele E P (atFin P k)) : AfE F E) = 1 + e * ((k : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) - 1) := by
  obtain ⟨h1, h0⟩ := idem_comp he h
  refine (afIso F E).injective (FiniteAdeleRing.ext _ fun Q => ?_)
  have e1 : afIso F E (1 + e * ((k : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) - 1)) Q =
      1 + afIso F E e Q * (algebraMap E (Q.adicCompletion E) (k : E) - 1) := by
    rw [map_add, map_mul, map_sub, map_one, afIso_tmul_one]; rfl
  rw [e1, GlobalTheory.Mem.ReadTwist.afIso_finAf_apply]
  by_cases hQ : Q = P
  · subst hQ
    rw [GlobalTheory.Mem.LocTriv.ev_local_self, h1, one_mul, add_sub_cancel]
    rfl
  · rw [GlobalTheory.Mem.LocTriv.ev_local_ne hQ, h0 Q hQ, zero_mul, add_zero]

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Local

end GlobalTheory.Core.Cls.JointsStd

end
end

