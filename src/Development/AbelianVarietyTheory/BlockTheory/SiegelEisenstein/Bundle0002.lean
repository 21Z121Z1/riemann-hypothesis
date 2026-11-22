import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.ConjugacyTypeUnfolding
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer
open Formalism.L2.SG.PoincareInHH Formalism.L2.SG.PoincareInHH.PoincareSetting
open Formalism.L2.SG.HidaSetting (HidaSetting rv incl)
open Formalism.L2.SG.InstExistsPf (instOf)
open Formalism.L2.SG.RowsJoinPinned (iotaX castGA)
open Formalism.MainNotions.S (AutInst uMat)
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyTypeUnfolding

variable {D : D7}

def castV {I I' : AutInst} (h : I = I') (x : Fin I.n → I.E) : Fin I'.n → I'.E := h ▸ x

def crdY {I : AutInst} (h : I = instOf D) (x : Fin I.n → I.E) : Fin (D.sp.Y 0).rank → D.host.E := castV h x

theorem fix_of_fix {I : AutInst} (h : I = instOf D) (x : Fin I.n → I.E) (g : GA D (D.sp.Y 0))
    (hg : Formalism.L2.Theta.mt (D.sp.Y 0) g *ᵥ ratV (crdY h x) = ratV (crdY h x)) :
    (∀ v, uMat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) g).1 v) *ᵥ rv I v x = rv I v x) ∧
      I.fmat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) g).2 *ᵥ incl I x = incl I x := by
  subst h
  obtain ⟨h1, h2⟩ := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have hs : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  have h1 := fun v => (h1 v).trans (congrArg (fun t => Formalism.L2.SG.AdBridge.ofHAInf (instOf D) t v) hs)
  have h2 := h2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (instOf D)) hs)
  have hg' : Formalism.L2.SG.AdBridge.hmat (instOf D) g *ᵥ (fun i => (1 : AF (instOf D).F) ⊗ₜ[(instOf D).F] x i) =
      fun i => (1 : AF (instOf D).F) ⊗ₜ[(instOf D).F] x i := hg
  have key : ∀ {R : Type} [CommRing R] (t : AF (instOf D).F ⊗[(instOf D).F] (instOf D).E →+* R),
      (Formalism.L2.SG.AdBridge.hmat (instOf D) g).map t *ᵥ (fun i => t ((1 : AF (instOf D).F) ⊗ₜ[(instOf D).F] x i)) =
        fun i => t ((1 : AF (instOf D).F) ⊗ₜ[(instOf D).F] x i) := by
    intro R _ t
    funext i
    have := congrArg t (congrFun hg' i)
    rw [RingHom.map_mulVec] at this
    exact this
  refine ⟨fun v => ?_, ?_⟩
  · change uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) *ᵥ _ = _
    have k := key (Formalism.L2.SG.AdBridge.thetaV (instOf D) v)
    simp only [Formalism.L2.SG.AdBridge.thetaV_tmul, map_one, one_mul] at k
    have hP : (instOf D).P v * ((instOf D).P v)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((instOf D).P_unit v))
    refine (congrArg (· *ᵥ rv (instOf D) v x) (h1 v)).trans ?_
    change (((instOf D).P v)⁻¹ * (Formalism.L2.SG.AdBridge.hmat (instOf D) g).map (Formalism.L2.SG.AdBridge.thetaV (instOf D) v) *
      (instOf D).P v) *ᵥ _ = _
    rw [rv, Matrix.mulVec_mulVec, Matrix.mul_assoc, hP, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, k]
  · change (instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ _ = _
    have k := key (Formalism.L2.SG.AdBridge.tauF (instOf D))
    simp only [Formalism.L2.SG.AdBridge.tauF_tmul] at k
    exact (congrArg (· *ᵥ incl (instOf D) x) h2).trans k

section Frame

variable (X : HidaSetting D) (h : X.B.I = instOf D) (u : D.what₂.Word) {V₀ A L : HSp D}
  (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)

structure IsFrame : Prop where
  e_eq : ∀ a i, d.e i a = crdY h (X.eR a) i
  f_eq : ∀ a i, d.e' i a = crdY h (X.fR a) i
  line : IsLineVec L ζ
  z_eq : d.i₀ *ᵥ vecB o ζ = crdY h (X.zR u)

variable {X h u d o ζ}

theorem embA_fix (hF : IsFrame X h u d o ζ) (a : GA D A) (x : Fin X.B.I.n → X.B.I.E) (hx : x ∈ fixSet X u) :
    Formalism.L2.Theta.mt (D.sp.Y 0) (embA d o a) *ᵥ ratV (crdY h x) = ratV (crdY h x) := by
  rcases hx with (⟨b, rfl⟩ | ⟨b, rfl⟩) | rfl
  · have e : ratV (crdY h (X.eR b)) = fun i => d.jX i b := funext fun i => congrArg (incA D) (hF.e_eq b i).symm
    rw [e]
    exact funext fun i => congrFun (congrFun (d.wittDecomp_anisotropicEmbedding_inclX (o.emb (a, 1))) i) b
  · have e : ratV (crdY h (X.fR b)) = fun i => d.jY i b := funext fun i => congrArg (incA D) (hF.f_eq b i).symm
    rw [e]
    exact funext fun i => congrFun (congrFun (d.wittDecomp_anisotropicEmbedding_inclY (o.emb (a, 1))) i) b
  · have e : Formalism.L2.Theta.mt (D.sp.Y 0) (embA d o a) ⬝ (d.j0 ⬝ o.jB) = d.j0 ⬝ o.jB := by
      rw [embA_apply, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jB, mt_one, Matrix.mul_one]
    rw [← hF.z_eq, vecB, ratV_mulVec, ratV_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact (congrArg (· *ᵥ ratV ζ) ((Matrix.mul_assoc _ _ _).trans e)).trans (Matrix.mulVec_mulVec _ _ _).symm

def toH (hF : IsFrame X h u d o ζ) (a : GA D A) : Hinf X u × Hfin X u :=
  (⟨(iotaX X h (embA d o a)).1, fun v x hx => (fix_of_fix h x _ (embA_fix hF a x hx)).1 v⟩,
   ⟨(iotaX X h (embA d o a)).2, fun x hx => (fix_of_fix h x _ (embA_fix hF a x hx)).2⟩)

def scalForm (hF : IsFrame X h u d o ζ) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (ξ : X.Vpi u) : GA D A → ℂ :=
  fun a => (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (toH hF a)

end Frame

def transl (X : HidaSetting D) (h : X.B.I = instOf D) (u : D.what₂.Word) (f : X.B.I.GA → ℂ) (y : X.B.I.Ginf) :
    GA D (D.sp.Y 0) → ℂ :=
  fun g => f (iotaX X h g * (y, X.xu u))

structure IsConjType (X : HidaSetting D) (f : X.B.I.GA → ℂ) : Prop where
  cont : Continuous f
  bdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  left : ∀ γ ∈ X.B.I.GFset, ∀ x, f (γ * x) = f x
  right : ∀ κ ∈ X.K2, ∀ x, f (x * (1, κ)) = star (X.chi2 κ) * f x

def thetaS (D : D7) : D.host.E := 1 / ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E)

section Per

variable {X : HidaSetting D} {h : X.B.I = instOf D} {u : D.what₂.Word} {V₀ A L : HSp D}
  {d : HypDec (D.sp.Y 0) V₀ D.R.rS} {o : OrthDec V₀ A L} {ζ : Fin L.rank → D.host.E}
  (hF : IsFrame X h u d o ζ) (hK : X.LevelSubgroupCharacter) (ψ : AddChar (AF D.host.F) ℂ)
  (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (ν : Measure (flagN d)) (𝓝 : Set (flagN d))
  (T : Cu X u hK) (f : X.B.I.GA → ℂ)

def perFun (y : X.B.I.Ginf) : GA D A → flagN d → ℂ :=
  besFun ψ (thetaS D) d o ζ (scalForm hF hK T (X.Wu u y)) (transl X h u f y)

def perAt (y : X.B.I.Ginf) : ℂ :=
  besPer ψ (thetaS D) d o ζ μ 𝓕 ν 𝓝 (scalForm hF hK T (X.Wu u y)) (transl X h u f y)

def Unfolds (Dt : Set X.B.I.GA) (c : ℝ) : Prop :=
  (∀ y, AbsConv μ 𝓕 ν 𝓝 (perFun hF hK ψ T f y)) ∧
  Integrable (perAt hF hK ψ μ 𝓕 ν 𝓝 T f) (X.nuQ u) ∧
  (∀ᵐ x ∂((X.B.I.muA X.B.μf).restrict X.B.fund), Summable fun δ : Dt => ‖Ph X u hK T ((δ : X.B.I.GA) * x)‖) ∧
  Integrable (fun x => f x * Pser X u hK Dt T x) ((X.B.I.muA X.B.μf).restrict X.B.fund) ∧
  ∫ x in X.B.fund, f x * Pser X u hK Dt T x ∂(X.B.I.muA X.B.μf) =
    (c : ℂ) * ∫ y, perAt hF hK ψ μ 𝓕 ν 𝓝 T f y ∂(X.nuQ u) ∧
  (MemLp (Pser X u hK Dt T) 2 ((X.B.I.muA X.B.μf).restrict X.B.fund) →
    ∀ φ : X.B.I.L2 X.B.μf X.B.fund, (φ : X.B.I.GA → ℂ) =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] (fun x => star (f x)) →
      ⟪φ, PuFun X u hK Dt T⟫_ℂ = (c : ℂ) * ∫ y, perAt hF hK ψ μ 𝓕 ν 𝓝 T f y ∂(X.nuQ u))

end Per

def Stmt : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = instOf D) (hK : X.LevelSubgroupCharacter)
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (u : D.what₂.Word) (V₀ A L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L)
      (ζ : Fin L.rank → D.host.E) (hF : IsFrame X h u d o ζ)
      (μ : Measure (GA D A)) (ν : Measure (flagN d)), μ.IsHaarMeasure → ν.IsHaarMeasure →
      ∃ c : ℝ, 0 < c ∧
        ∀ (𝓕 : Set (GA D A)) (𝓝 : Set (flagN d)), IsFundamentalDomain (GQ A) 𝓕 μ →
          IsFundamentalDomain (NFlagQ (D.sp.Y 0) d.e) 𝓝 ν →
          ∀ Dt : Set X.B.I.GA, IsReps X u Dt →
            ∀ (T : Cu X u hK) (f : X.B.I.GA → ℂ), IsConjType X f → Unfolds hF hK ψ μ 𝓕 ν 𝓝 T f Dt c

example (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (Dt : Set X.B.I.GA) (T : Cu X u hK) (f : X.B.I.GA → ℂ)
    (hm : MemLp (Pser X u hK Dt T) 2 ((X.B.I.muA X.B.μf).restrict X.B.fund)) (φ : X.B.I.L2 X.B.μf X.B.fund)
    (hφ : (φ : X.B.I.GA → ℂ) =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] (fun x => star (f x))) :
    ⟪φ, PuFun X u hK Dt T⟫_ℂ = ∫ x in X.B.fund, f x * Pser X u hK Dt T x ∂(X.B.I.muA X.B.μf) := by
  have e : PuFun X u hK Dt T = hm.toLp _ := dif_pos hm
  rw [e, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hφ, hm.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

example {X : HidaSetting D} {h : X.B.I = instOf D} {u : D.what₂.Word} {V₀ A L : HSp D} {d : HypDec (D.sp.Y 0) V₀ D.R.rS}
    {o : OrthDec V₀ A L} {ζ : Fin L.rank → D.host.E} (hF : IsFrame X h u d o ζ) : toH hF 1 = 1 := by
  have e : iotaX X h (embA d o 1) = 1 := by rw [map_one, map_one]
  exact Prod.ext (Subtype.ext (congrArg Prod.fst e)) (Subtype.ext (congrArg Prod.snd e))

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyTypeUnfolding

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.ModelFrames
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModelFrames

variable {D : D7}

section Local

variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

def rowMat (c p : ℕ) (u : n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks 0 0 (Matrix.of fun l s => if l.val + 1 = p then u s else 0) 0

def scal (γ : kˣ) (κ : ℕ → k) (t₁ : kˣ) (i : ℕ) : k := (t₁ : k) * ∏ j ∈ Finset.range i, κ j * ((γ⁻¹ : kˣ) : k)

def coef (σ : ℕ) (a : k) (i : ℕ) : k := if i < σ then 1 else if i = σ then a else -1

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

def opRow (χ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Fin 1) n' k) : ℂ :=
  GlobalTheory.RootEx.opE χ ν p (fun y => Φ (y + rowMat c p (x (Sum.inr 0)))) (x.submatrix Sum.inl id)

end Local

def jacobiWittDecomposition {S S₀ : HSp D} {σ : ℕ} (d : HypDec S S₀ (σ + 1)) (i : Fin (2 * σ + 1 + 1)) : Fin S.rank → D.host.E :=
  fun r => if h : i.val < σ + 1 then d.e r ⟨i.val, h⟩ else d.e' r ⟨2 * σ + 1 - i.val, by omega⟩

def besselWittDecomposition {S S₀ : HSp D} {σ : ℕ} (d : HypDec S S₀ σ) (z : Fin S₀.rank → D.host.E) (i : Fin (2 * σ + 1)) :
    Fin S.rank → D.host.E :=
  fun r => if h : i.val < σ then d.e r ⟨i.val, h⟩ else if h' : i.val = σ then (d.i₀ *ᵥ z) r
    else d.e' r ⟨2 * σ - i.val, by omega⟩

def normZ {σ : ℕ} (B : BesLev D σ) : D.host.E := star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def loc (p : SplitPt D k) (a : D.host.E) : k := p.pr (incA D a)

def up {S T : HSp D} (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : WO S T :=
  Matrix.map ((β.b * x : Matrix (Fin T.rank) n' k) * α.b' : Matrix (Fin T.rank) (Fin S.rank) k) p.sec

def IsModel (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (α : Frame p S n') (β : Frame p T n)
    (I : SB (Matrix n n' k) →ₗ[ℂ] (WO S T → ℂ)) : Prop :=
  (∀ Φ, IsThetaFunO ψ S T (I Φ)) ∧
  (∀ t : WO S T, IsHalf p.e t → ∀ Φ Φ' : SB (Matrix n n' k), (∀ x, Φ'.1 x = Φ.1 (x + rd α β t)) →
    I Φ' = heisO ψ S T t (I Φ)) ∧
  ∀ t : WO S T, IsHalf (cA D p.e) t → ∀ Φ Φ' : SB (Matrix n n' k),
    (∀ x, Φ'.1 x = ψ (symplO S T (up α β x) t) * Φ.1 x) → I Φ' = heisO ψ S T t (I Φ)

def IsNormalJac {σ : ℕ} (J : JacLev D (σ + 1)) (N : D.host.E) (γ t₁ : kˣ) (α₀ : Frame p J.W₀ n')
    (α : Frame p J.W (n' ⊕ Fin (2 * σ + 1 + 1))) : Prop :=
  (∀ r j, α.b r (Sum.inl j) = (J.d.j0.map p.pr * α₀.b : Matrix _ n' k) r j) ∧
    ∀ r i, α.b r (Sum.inr i) = scal γ (coef σ (loc p (-(D.host.xi0 * N)))) t₁ i.val * loc p (jacobiWittDecomposition J.d i r)

def IsNormalBes {σ : ℕ} (B : BesLev D σ) (γ t₁ : kˣ) (β₁ : Frame p B.A n) (β : Frame p B.V (n ⊕ Fin (2 * σ + 1))) : Prop :=
  (∀ r j, β.b r (Sum.inl j) = ((B.d.j0 * B.o.jA : Mx D _ _).map p.pr * β₁.b : Matrix _ n k) r j) ∧
    ∀ r i, β.b r (Sum.inr i) =
      scal γ (coef σ (loc p (-normZ B))) t₁ i.val * loc p (besselWittDecomposition B.d (vecB B.o B.ζ) i r)

def IsCoreFrame {σ : ℕ} (B : BesLev D σ) (γ t₁ : kˣ) (β₁ : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) : Prop :=
  (∀ r j, β₀.b r (Sum.inl j) = (B.o.jA.map p.pr * β₁.b : Matrix _ n k) r j) ∧
    ∀ r, β₀.b r (Sum.inr 0) = scal γ (coef σ (loc p (-normZ B))) t₁ σ * loc p (vecB B.o B.ζ r)

end Frames

def FlatSplitFB (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (p : SplitPt D k) (χ : AddChar k Circle) (γ t₁ : kˣ) (ν : Measure k), ν.IsAddHaarMeasure →
    (∀ a, (χ a : ℂ) = psiE ψ (p.sec ((γ : k) * a))) →
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
      (α₀ : Frame p J.W₀ n') (α : Frame p J.W (n' ⊕ Fin (2 * σ + 1 + 1)))
      (β₁ : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (β : Frame p B.V (n ⊕ Fin (2 * σ + 1))),
      IsNormalJac J (normZ B) γ t₁ α₀ α → IsNormalBes B γ t₁ β₁ β → IsCoreFrame B γ t₁ β₁ β₀ →
      ∀ I : SB (Matrix (n ⊕ Fin (2 * σ + 1)) (n' ⊕ Fin (2 * σ + 1 + 1)) k) →ₗ[ℂ] (WO J.W B.V → ℂ), IsModel ψ α β I →
        ∃ I₀ : SB (Matrix (n ⊕ Fin 1) n' k) →ₗ[ℂ] (WO J.W₀ B.V₀ → ℂ), IsModel ψ α₀ β₀ I₀ ∧
          ∀ Φ, ∃ h : opRow χ ν (σ + 1) Φ.1 ∈ SB (Matrix (n ⊕ Fin 1) n' k), flatFB s (I Φ) = I₀ ⟨_, h⟩

example {k : Type} [Field k] (γ t₁ : kˣ) (κ : ℕ → k) (i : ℕ) : (γ : k) * scal γ κ t₁ (i + 1) = κ i * scal γ κ t₁ i := by
  simp only [scal, Finset.prod_range_succ, Units.val_inv_eq_inv_val]
  field_simp

example {k : Type} [Field k] (a : k) : (scal 1 (coef 1 a) 1 0, scal 1 (coef 1 a) 1 1, scal 1 (coef 1 a) 1 2,
    scal 1 (coef 1 a) 1 3) = (1, 1, a, -a) := by
  simp [scal, coef, Finset.prod_range_succ]

end GlobalTheory.IndefiniteRowSideFullHecke.ModelFrames

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.SeeSawFourier
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier

variable {D : D7}

def nrm (L : HSp D) (ζ : Fin L.rank → D.host.E) : D.host.E := star ζ ⬝ᵥ L.gram *ᵥ ζ

def colQ {m : ℕ} (ζ : Fin m → D.host.E) : Matrix (Fin m) (Fin 1) D.host.E := replicateCol (Fin 1) ζ

def beta (S : HSp D) {L L'' : HSp D} (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E) (x : WO L S) : WO S L'' :=
  (rat (colQ ζ) : Mx D L''.rank 1) ⬝
    (adj (incA D (nrm L'' ζ)⁻¹ • (x ⬝ (rat (colQ ζ₁) : Mx D L.rank 1) : Mx D S.rank 1)) ⬝ gA S : Mx D 1 S.rank)

def OppLines (L L'' : HSp D) (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E) : Prop :=
  IsLineVec L ζ₁ ∧ IsLineVec L'' ζ ∧ nrm L ζ₁ = -nrm L'' ζ

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def weilChar (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (a : k) : ℂ := psiE ψ (incA D D.host.xi0 * p.sec a)

variable {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def atW (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : WO S T :=
  Matrix.map (β.b ⬝ (x ⬝ α.b') : Matrix (Fin T.rank) (Fin S.rank) k) p.sec

def IsModel (ψ : AddChar (AF D.host.F) ℂ) (α : Frame p S n') (β : Frame p T n)
    (M : (Matrix n n' k → ℂ) →ₗ[ℂ] (WO S T → ℂ)) : Prop :=
  ∀ Φ ∈ SB (Matrix n n' k), IsThetaFunO ψ S T (M Φ) ∧
    (∀ a : Matrix n n' k, M (fun x => Φ (x + a)) = heisO ψ S T (atW α β a) (M Φ)) ∧
    ∀ a' : WO S T, IsHalf (cA D p.e) a' →
      M (fun x => ψ (symplO S T (atW α β x) a') * Φ x) = heisO ψ S T a' (M Φ)

def IsLineFrame {L : HSp D} (ζ : Fin L.rank → D.host.E) (α : Frame p L (Fin 1)) : Prop :=
  α.b = replicateCol (Fin 1) fun i => p.pr (ratV ζ i)

def ofCol (f : (n → k) → ℂ) (x : Matrix n (Fin 1) k) : ℂ := f fun i => x i 0

def ofRow (g : (n → k) → ℂ) (x : Matrix (Fin 1) n k) : ℂ := g (x 0)

variable [MeasurableSpace k] [BorelSpace k]

def hat (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (ν : Measure k) (f : (n → k) → ℂ) (η : n → k) : ℂ :=
  ∫ y, f y * weilChar p ψ (-(η ⬝ᵥ y)) ∂(Measure.pi fun _ => ν)

end Local

def LineFourier (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (S L L'' : HSp D) (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E), OppLines L L'' ζ₁ ζ →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (b : Frame p S n) (a₁ : Frame p L (Fin 1))
    (a : Frame p L'' (Fin 1)), IsLineFrame ζ₁ a₁ → IsLineFrame ζ a →
  ∀ M₁ : (Matrix n (Fin 1) k → ℂ) →ₗ[ℂ] (WO L S → ℂ), IsModel ψ a₁ b M₁ →
    ∃ M₂ : (Matrix (Fin 1) n k → ℂ) →ₗ[ℂ] (WO S L'' → ℂ), IsModel ψ b a M₂ ∧
      ∀ f ∈ SB (n → k), hat p ψ ν f ∈ SB (n → k) ∧
        ∀ x : WO L S, M₂ (ofRow (hat p ψ ν f)) (beta S ζ₁ ζ x) = M₁ (ofCol f) x

def SeeSawFourier (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E), OppLines L L'' ζ₁ ζ →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (p : SplitPt D k) (n nA nT : Type) [Fintype n] [DecidableEq n] [Fintype nA] [DecidableEq nA] [Fintype nT]
    [DecidableEq nT] (b : Frame p S n) (bA : Frame p A nA) (b₀ : Frame p V₀ (nA ⊕ Fin 1)) (bT : Frame p T nT)
    (bX : Frame p X (nT ⊕ Fin 1)), IsSumFrame o ζ₁ bA b₀ → IsSumFrame o'' ζ bT bX →
  ∀ (M₁ : (Matrix n (nA ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (WO V₀ S → ℂ)) (M₂ : (Matrix nT n k → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsModel ψ b₀ b M₁ → IsModel ψ b bT M₂ →
    ∃ N : (Matrix n nA k → ℂ) →ₗ[ℂ] (Matrix (nT ⊕ Fin 1) n k → ℂ) →ₗ[ℂ] (WO A S × WO S X → ℂ),
      (∀ Θ ∈ SB (Matrix (nT ⊕ Fin 1) n k), ∀ w : WO S X,
        IsModel ψ bA b ((LinearMap.funLeft ℂ ℂ fun u : WO A S => (u, w)).comp (N.flip Θ))) ∧
      (∀ Ψ ∈ SB (Matrix n nA k), ∀ u : WO A S,
        IsModel ψ b bX ((LinearMap.funLeft ℂ ℂ fun w : WO S X => (u, w)).comp (N Ψ))) ∧
      ∀ f ∈ SB (n → k), hat p ψ ν f ∈ SB (n → k) ∧ ∀ Ψ ∈ SB (Matrix n nA k), ∀ Φ ∈ SB (Matrix nT n k),
        ∀ (u : WO A S) (x' : WO S T) (x : WO L S),
          N Ψ (tensRow Φ (hat p ψ ν f)) (u, (o''.resT S).symm (x', beta S ζ₁ ζ x)) =
            M₂ Φ x' * M₁ (tensCol Ψ f) ((o.resS S).symm (u, x))

section Checks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.WeightedNormColumns
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormColumns

section Scalars

variable {k : Type} [Field k]

def kaSrc (ρ : ℕ) (N : k) (i : ℕ) : k := if i < ρ then 1 else if i = ρ then -N else -1

def kaTgt (ρ : ℕ) (cst : k) (i : ℕ) : k := if i + 1 < ρ then 1 else if i + 1 = ρ then cst else -1

def IsNormalScal (ξ : k) (κ : ℕ → k) {c : ℕ} (t : Fin c → k) : Prop :=
  ∀ i j : Fin c, j.val = i.val + 1 → t j = ξ⁻¹ * κ i.val * t i

end Scalars

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def xiW (p : SplitPt D k) : k := p.pr (incA D D.host.xi0)

def IsWeilChar (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) : Prop :=
  ∀ a, (χ a : ℂ) = psiE ψ (p.sec (xiW p * a))

def normW (p : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) : k := p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))

def srcVec (p : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) (s : Fin (2 * ρ + 1)) (r : Fin B.V.rank) : k :=
  if h : s.val < ρ then p.pr (B.d.jX r ⟨s.val, h⟩)
  else if h' : s.val = ρ then p.pr ((B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) r)
  else p.pr (B.d.jY r ⟨2 * ρ - s.val, by have := s.2; omega⟩)

def tgtVec (p : SplitPt D k) {ρ : ℕ} (J : JacLev D ρ) (s : Fin (2 * ρ)) (r : Fin J.W.rank) : k :=
  if h : s.val < ρ then p.pr (J.d.jX r ⟨s.val, h⟩)
  else (xiW p)⁻¹ * p.pr (J.d.jY r ⟨2 * ρ - 1 - s.val, by have := s.2; omega⟩)

variable {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def NormalBF {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (αA : Frame p B.A n') (β₀ : Frame p J.W₀ n)
    (α : Frame p B.V (n' ⊕ Fin (2 * ρ + 1))) (β : Frame p J.W (n ⊕ Fin (2 * ρ))) : Prop :=
  ∃ (t' : Fin (2 * ρ + 1) → k) (t : Fin (2 * ρ) → k),
    IsNormalScal (xiW p) (kaSrc ρ (normW p B)) t' ∧ IsNormalScal (xiW p) (kaTgt ρ (normW p B)) t ∧
    t' ⟨ρ, by omega⟩ = 1 ∧ (∀ i : Fin (2 * ρ), i.val = 0 → t i = t' 0) ∧
    α.b = fromCols ((B.d.j0 * B.o.jA).map p.pr * αA.b) (Matrix.of fun r s => t' s * srcVec p B s r) ∧
    β.b = fromCols (J.d.j0.map p.pr * β₀.b) (Matrix.of fun r s => t s * tgtVec p J s r)

def IsModel (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m']
    [DecidableEq m'] (α : Frame p S m') (β : Frame p T m) (M : SB (Matrix m m' k) →ₗ[ℂ] (WO S T → ℂ)) : Prop :=
  (∀ Φ, IsThetaFunO ψ S T (M Φ)) ∧
  (∀ x : WO S T, IsHalf p.e x → ∀ Φ Φ' : SB (Matrix m m' k),
    (∀ u, Φ'.1 u = Φ.1 (u + rd α β x)) → M Φ' = heisO ψ S T x (M Φ)) ∧
  (∀ y : WO S T, IsHalf (cA D p.e) y → ∀ Φ Φ' : SB (Matrix m m' k),
    (∀ u : WO S T, IsHalf p.e u → Φ'.1 (rd α β u) = ψ (symplO S T u y) * Φ.1 (rd α β u)) →
      M Φ' = heisO ψ S T y (M Φ))

def zCol (n' : Type) (ρ : ℕ) (b : n → k) : Matrix (n ⊕ Fin (2 * ρ)) (n' ⊕ Fin (2 * ρ + 1)) k :=
  fromBlocks 0 (Matrix.of fun r i => if i.val = ρ then b r else 0) 0 0

variable [MeasurableSpace k] [BorelSpace k]

def flatE (χ : AddChar k Circle) (ν : Measure k) (ρ : ℕ)
    (Φ : Matrix (n ⊕ Fin (2 * ρ)) (n' ⊕ Fin (2 * ρ + 1)) k → ℂ) (x : Matrix n (n' ⊕ Fin 1) k) : ℂ :=
  GlobalTheory.RootEx.opE χ ν (ρ + 1) (fun y => Φ (y + zCol n' ρ fun r => x r (Sum.inr 0))) (x.submatrix id Sum.inl)

omit [Fintype n] [DecidableEq n] in
theorem zCol_zero (ρ : ℕ) : zCol n' ρ (fun _ : n => (0 : k)) = 0 := by
  ext (r | r) (s | s) <;> simp [zCol]

theorem flatE_zero (χ : AddChar k Circle) (ν : Measure k) (ρ : ℕ)
    (Φ : Matrix (n ⊕ Fin (2 * ρ)) (n' ⊕ Fin (2 * ρ + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    flatE χ ν ρ Φ (fromCols x₀ 0) = GlobalTheory.RootEx.opE χ ν (ρ + 1) Φ x₀ := by
  have h : (fun r => fromCols x₀ (0 : Matrix n (Fin 1) k) r (Sum.inr 0)) = fun _ => 0 := rfl
  rw [flatE, h, zCol_zero]
  simp only [add_zero]
  rfl

def FlatSplitBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (p : SplitPt D k) (χ : AddChar k Circle), IsWeilChar p ψ χ →
    ∀ (ν : Measure k), ν.IsAddHaarMeasure →
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
      (αA : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β₀ : Frame p J.W₀ n)
      (α : Frame p B.V (n' ⊕ Fin (2 * ρ + 1))) (β : Frame p J.W (n ⊕ Fin (2 * ρ))),
      IsSumFrame B.o B.ζ αA α₀ → NormalBF B J αA β₀ α β →
      ∀ M : SB (Matrix (n ⊕ Fin (2 * ρ)) (n' ⊕ Fin (2 * ρ + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ), IsModel ψ α β M →
        ∃ M₀ : SB (Matrix n (n' ⊕ Fin 1) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ), IsModel ψ α₀ β₀ M₀ ∧
          ∀ Φ : SB (Matrix (n ⊕ Fin (2 * ρ)) (n' ⊕ Fin (2 * ρ + 1)) k),
            ∃ h : flatE χ ν ρ Φ.1 ∈ SB (Matrix n (n' ⊕ Fin 1) k), flatBF s (M Φ) = M₀ ⟨flatE χ ν ρ Φ.1, h⟩

example {k : Type} [Field k] (ξ N : k) (hξ : ξ ≠ 0) : IsNormalScal ξ (kaSrc 1 N) ![ξ, 1, -(ξ⁻¹ * N)] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [kaSrc]

example {k : Type} [Field k] (ξ N : k) (hξ : ξ ≠ 0) : IsNormalScal ξ (kaTgt 1 N) ![ξ, N] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [kaTgt]
  field_simp

end GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormColumns

end
end

