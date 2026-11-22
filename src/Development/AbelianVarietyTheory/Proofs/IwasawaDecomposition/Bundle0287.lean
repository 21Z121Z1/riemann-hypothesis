import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0268
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapOpOfKForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.GoodProj

theorem rowForm_rE {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {s : ℕ}
    (ok : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) (x : Fin (rDim D A P ψ t) → D.what₂.LL) :
    rowForm A P ψ t ((rE D A P ψ t).mulVec x) =
      (A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X) (rowForm A P ψ t x) := by
  have hc := (idempotent_spec _ A.v0 ok.conj G A.X ok.irr).2
  have h1 := (level_operator_spec _ A.v0 ok.conj (A.fam.R t).S ((ok.what₂ t).hpos A.v0) G (A.fam.R t).r (ok.what₂ t).act
    (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ (idemOf A.X) (hc _).symm).1
  unfold rowForm rE
  change _ = (A.fam.R t).S.gaOp (A.fam.R t).r (idemOf A.X) _
  rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, CSD.gaMat, Matrix.sum_mulVec, map_sum]
  rw [CSD.gaOp]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.smul_mulVec, map_smul]
  exact congrArg _ (Subtype.ext (action_matrix_spec _ (A.fam.R t).S G (A.fam.R t).r g _))

end GlobalTheory.Mem.R3.GoodProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableChernPolyTopDensity
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.ChernMeas

def measPoly (X σ : Type) [MeasurableSpace X] : Subalgebra ℝ (X → MvPolynomial σ ℂ) where
  carrier := {f | ∀ d, Measurable fun x => coeff d (f x)}
  mul_mem' := by
    classical
    intro f g hf hg d
    simp only [Pi.mul_apply, coeff_mul]
    exact Finset.measurable_sum _ fun p _ => (hf p.1).mul (hg p.2)
  add_mem' := by
    intro f g hf hg d
    simp only [Pi.add_apply, coeff_add]
    exact (hf d).add (hg d)
  algebraMap_mem' := by
    intro c d
    exact measurable_const (a := coeff d (algebraMap ℝ (MvPolynomial σ ℂ) c))

theorem C_mem {X σ : Type} [MeasurableSpace X] {f : X → ℂ} (hf : Measurable f) :
    (fun x => (C (f x) : MvPolynomial σ ℂ)) ∈ measPoly X σ := by
  classical
  intro d
  simp only [coeff_C]
  split_ifs
  · exact hf
  · exact measurable_const

theorem const_mem {X σ : Type} [MeasurableSpace X] (p : MvPolynomial σ ℂ) :
    (fun _ : X => p) ∈ measPoly X σ := fun _ => measurable_const

def evalAt {X σ : Type} [MeasurableSpace X] (x : X) : measPoly X σ →ₐ[ℝ] MvPolynomial σ ℂ :=
  (Pi.evalAlgHom ℝ (fun _ : X => MvPolynomial σ ℂ) x).comp (measPoly X σ).val

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r A) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem measurable_curv {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (ξ η : V n) (i j : r) :
    Measurable fun v => curv G v ξ η i j := by
  let f : V n → ℂ := fun x => conn G x ξ i j
  change Measurable fun v => -((1 / 2 : ℂ) * (fderiv ℝ f v η + Complex.I * fderiv ℝ f v (Complex.I • η)))
  exact (((measurable_fderiv_apply_const ℝ f η).add
    ((measurable_fderiv_apply_const ℝ f (Complex.I • η)).const_mul _)).const_mul _).neg

theorem curvPoly_mem {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (i j : r) :
    (fun v => curvPoly G v i j) ∈ measPoly (V n) (Fin n × Fin n) := by
  have e : (fun v => curvPoly G v i j) = ∑ a, ∑ b, (fun v => (C (curv G v (coordVec a) (coordVec b) i j) :
      MvPolynomial (Fin n × Fin n) ℂ)) * fun _ => X (a, b) := by
    funext v
    simp [curvPoly, Finset.sum_apply]
  rw [e]
  exact Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ =>
    Subalgebra.mul_mem _ (C_mem (measurable_curv G _ _ i j)) (const_mem _)

theorem chernPoly_mem {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (k : ℕ) :
    (fun v => chernPoly G v k) ∈ measPoly (V n) (Fin n × Fin n) := by
  let M : Matrix r r (measPoly (V n) (Fin n × Fin n)) := Matrix.of fun i j => ⟨_, curvPoly_mem G i j⟩
  have e : (fun v => chernPoly G v k) = ((Matrix.charpolyRev (-M)).coeff k).1 := by
    funext v
    have h : -curvPoly G v = (-M).map (evalAt v).toRingHom := by
      ext i j : 2
      rfl
    rw [chernPoly, h, charpolyRev_map, Polynomial.coeff_map]
    rfl
  rw [e]
  exact Subtype.property _

theorem measurable_chernTop {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ) :
    Measurable (fun v => chernTop R G v) := by
  let P : measPoly (V n) (Fin n × Fin n) :=
    aeval (fun x : ι × ℕ => (⟨_, chernPoly_mem (fun u => G u x.1) x.2⟩ : measPoly (V n) (Fin n × Fin n))) R
  have e (v : V n) : aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R = P.1 v := by
    change _ = evalAt v P
    rw [← AlgHom.comp_apply, comp_aeval]
    rfl
  simp only [chernTop, e, topCoeff]
  refine Measurable.const_mul (Complex.measurable_re.comp ?_) _
  exact Finset.measurable_sum _ fun w _ => (P.2 _).const_mul _

end GlobalTheory.ChernMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.FormSym

theorem mem_FiC_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (lam : ι → DomWeight n)
    {c c' : Type} (yc : c → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (e : c' → c) (he : Function.Surjective e)
    (g : c → Frames (gramC J emb) → ℂ) :
    g ∘ e ∈ FiC S emb lam (yc ∘ e) ↔ g ∈ FiC S emb lam yc := by
  simp only [FiC, Submodule.mem_map]
  constructor
  · rintro ⟨h, hh, he'⟩
    refine ⟨h, hh, ?_⟩
    funext x
    obtain ⟨x', rfl⟩ := he x
    exact congrFun he' x'
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

section Gen

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {Ch : Type} {chOf : (D.mem u).C.cls i → Ch}

def clsOfChart (β : Ch) (hβ : ∀ c, chOf c = β)
    (K : LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) : ClsTied u i hi where
  lev := K.lev
  y c := K.y ⟨c, hβ c⟩
  y_bij := K.y_bij.comp (f := fun c : (D.mem u).C.cls i => (⟨c, hβ c⟩ : {c // chOf c = β}))
    ⟨fun _ _ h => congrArg Subtype.val h, fun c => ⟨c.1, rfl⟩⟩
  y_lat c := K.y_lat ⟨c, hβ c⟩
  stabI c := K.stabI ⟨c, hβ c⟩
  stabI_inj c := K.stabI_inj ⟨c, hβ c⟩
  stabI_range c := K.stabI_range ⟨c, hβ c⟩

set_option maxHeartbeats 4000000 in

def valOfG [Subsingleton Ch] (eV : (D.mem u).A.vT ≃ PlT D u)
    (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) (β : Ch) (hβ : ∀ c, chOf c = β)
    (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (hde : ∃ C : GL (Fin (D.R.N i)) D.host.E,
      cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
      (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
      ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eY z).1 τ).det)
    (hV : ValuationCompatibleChart (D.fm u) eY (fun _ => True) chOf (lat := fun c => clsCrd D u i hi c) K)
    (hI : IpVTieG (D.fm u) eY)
    (hD : DilationCompatibleChart (D.fm u) eY eV chOf (lat := fun c => clsCrd D u i hi c) K) :
    ValTied u eV i hi (clsOfChart β hβ (K β)) where
  eY := eY
  de := hde
  Fi φ := by
    rw [hV.Fi φ]
    constructor
    · intro h
      exact (mem_FiC_comp _ _ _ (K β).y (fun c => (⟨c, hβ c⟩ : {c // chOf c = β})) (fun c => ⟨c.1, rfl⟩) _).2 (h β)
    · intro h β'
      obtain rfl : β = β' := Subsingleton.elim _ _
      exact (mem_FiC_comp _ _ _ (K β).y (fun c => (⟨c, hβ c⟩ : {c // chOf c = β})) (fun c => ⟨c.1, rfl⟩) _).1 h
  ipV := hI
  rat := hV.rat
  lat x := by
    constructor
    · intro hx w
      exact (hV.lat w trivial x).1 (Submodule.subset_span hx)
    · intro h
      exact GlobalTheory.LvT.mem_of_forall_locW D _ (fun w => (hV.lat w trivial x).2 (h w))
  dil v a k hk c δ hδ := hD.dil v a k hk β ⟨c, hβ c⟩ δ hδ
  dilT v a k hk c δ hδ g hg := hD.dilT v a k hk β ⟨c, hβ c⟩ δ hδ g hg

set_option maxHeartbeats 4000000 in

def lvOfG (A : AtTTied u) (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T A.res i hi (fun c => clsCrd D u i hi c)) :
    LvTied u A i hi where
  pr := L.pr
  pr_surj := L.pr_surj
  pr_smul := L.pr_smul
  pr_ker := L.pr_ker
  fv_ker := L.fv_ker
  prk := L.prk
  prk_surj := L.prk_surj
  prk_smul := L.prk_smul
  prk_ker := L.prk_ker
  te := L.te

variable (A : AtTTied u) (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T A.res i hi (fun c => clsCrd D u i hi c))
  (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) (β : Ch) (hβ : ∀ c, chOf c = β)

set_option maxHeartbeats 4000000 in
theorem fvOfG (fMe : ∀ β v, (K β).lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (h : FvTieG L A.eV K fMe) :
    FvTie (lvOfG A L) (clsOfChart β hβ (K β)) (fMe β) :=
  fun v c z hz => h v β ⟨c, hβ c⟩ z hz

set_option maxHeartbeats 4000000 in
theorem upOfG (eY : (D.mem u).C.Y i ≃ Fr D i hi) (W : ValTied u A.eV i hi (clsOfChart β hβ (K β))) (hY : W.eY = eY)
    (h : UpNatTieG L eY A.eV K) : UpNatTie (lvOfG A L) (clsOfChart β hβ (K β)) W := by
  intro v c z hz
  obtain ⟨_, γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := h v β ⟨c, hβ c⟩ z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun g s s' hs => ?_⟩
  rw [hY] at hs
  exact h6 g s s' hs

set_option maxHeartbeats 4000000 in
theorem dnOfG (eY : (D.mem u).C.Y i ≃ Fr D i hi) (W : ValTied u A.eV i hi (clsOfChart β hβ (K β))) (hY : W.eY = eY)
    (h : DnNatTieG L eY A.eV K) : DnNatTie (lvOfG A L) (clsOfChart β hβ (K β)) W := by
  intro v c g hg
  obtain ⟨_, γ, η, κ, h1, h2, h3, h4, h6⟩ := h v β ⟨c, hβ c⟩ g hg
  refine ⟨γ, η, κ, h1, h2, h3, h4, fun f s s' hs => ?_⟩
  rw [hY] at hs
  exact h6 f s s' hs

end Gen

section Gen2

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 4000000 in
theorem normOfG {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u i hi} (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (W : ValTied u eV i hi K) (hY : W.eY = eY) (h : NormTieG (D.fm u) eY) : NormTie W := by
  intro s x Pc hPc o ho
  rw [hY] at hPc
  exact h s x Pc hPc o ho

set_option maxHeartbeats 4000000 in
theorem bwOfG (A : AtTTied u) {K : ClsTied u i hi} (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (W : ValTied u A.eV i hi K) (hY : W.eY = eY)
    (h : BwTieG (D.fm u) (D.mem u).A.T A.res eY (fun c => clsCrd D u i hi c)) : BwTie A W := by
  intro w hw hs v x
  rw [hY]
  exact h w hw hs v x

end Gen2

set_option maxHeartbeats 4000000 in

theorem readsK_one {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {u : B.Word} {a : I.ι}
    {i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))} (h : I.ReadsK l Z u a i hi chOf K) (β : Ch)
    (hβ : ∀ c, chOf c = β) :
    ∃ k, I.Reads u a i (fun _ => ()) (fun _ => (K β).lev.Lb) (fun _ => (K β).lev.U) (fun _ => (K β).lev.chi)
      (fun c => ((K β).y ⟨c, hβ c⟩).1) (fun c s => ((K β).stabI ⟨c, hβ c⟩ s).1) k := by
  obtain rfl : chOf = fun _ => β := funext hβ
  obtain ⟨k, hk⟩ := h
  refine ⟨fun _ => k β, ⟨fun c c' => ⟨fun _ => (hk.key c c').1 rfl, fun _ => rfl⟩, fun _ => ?_, fun _ => hk.lb β,
    fun _ => hk.k_std β, fun _ => hk.k_off β, fun _ => hk.k_T β, hk.pt, hk.lev, hk.chr, hk.stab⟩⟩
  obtain ⟨c, _⟩ := hk.onto β
  exact ⟨c, rfl⟩

end GlobalTheory.Mem.FormSym

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelGroupFaceLevelIffFlagGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.TopBridge

variable {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

theorem rangeRestrict_mem_Q_iff (κ : GA D V) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q ↔ Lev.finE V κ ∈ parLev D.sp.cm V.gram β L := by
  have e1 : Lev.finE V κ = Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 := Lev.finE_eq V κ
  constructor
  · intro h
    have h1 : Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 ∈ lev D.sp.cm V.gram β (Lev.flagL L) := h
    rw [e1]
    exact h1.1
  · intro h
    have h1 : Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 ∈ lev D.sp.cm V.gram β (Lev.flagL L) := by
      rw [mem_lev]
      exact ⟨e1 ▸ h, Subgroup.mem_top _⟩
    exact h1

theorem mem_levelSubgroup_withP_iff (P : LevelP L.Pg L.r ℂ) {κ : GA D V} (hκ : κ ∈ GfC V) :
    κ ∈ levS V β (Lev.withP L P) ↔ Lev.finE V κ ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (Lev.finE V κ) ∈ P.H :=
  ⟨fun h => h.2, fun h => ⟨hκ, h⟩⟩

theorem levelCharacter_withLevel_of_mem {P : LevelP L.Pg L.r ℂ} {κ : GA D V} (hp : rTup β L (Lev.finE V κ) ∈ P.H) :
    Lev.levChi V β (Lev.withP L P) κ = ((P.chi ⟨_, hp⟩ : ℂˣ) : ℂ) * Lev.levChi V β (Lev.flagL L) κ := by
  unfold Lev.levChi
  rw [Lev.levFn_withP, extendOne_of_mem _ hp, Units.val_mul]

theorem levChi_flagL_eq_ch {κ : GA D V} (hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q) :
    Lev.levChi V β (Lev.flagL L) κ = (((levEnv V β L).ch ⟨_, hq⟩ : ℂˣ) : ℂ) := by
  have e2 : (levEnv V β L).ch ⟨_, hq⟩ = levFn β (Lev.flagL L) (Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1) := rfl
  unfold Lev.levChi
  rw [e2, Lev.finE_eq]
  rfl

end GlobalTheory.TopBridge

open GlobalTheory.TopBridge in

theorem GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_red_R → ∀ (b : Bool) (t : T) (κ : GA D D.sp.X'), κ ∈ GfC D.sp.X' → ((κ ∈ levS _ R.βX (datXP R t (R.levR F b)) ↔ ∃ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q, (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P) ∧ ∀ (hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hp : (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P), levChi _ R.βX (datXP R t (R.levR F b)) κ = ((levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hq⟩ : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hp⟩ : D.what₂.LLˣ) : D.what₂.LL)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hr b t κ hκ
  have hQ : ∀ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q,
      (R.B.R t).act_tie.red ⟨_, hq⟩ = R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)) := fun hq =>
    R.eG.eq_symm_apply.2 ((hr t ⟨_, hq⟩).trans (congrArg (rTup R.βX (R.datXt t)) (Lev.finE_eq D.sp.X' κ).symm))
  have hH : ∀ x, x ∈ (R.levR F b).H ↔ R.eG.symm x ∈ (F.lvl b).P := fun x => Iff.rfl
  have hS := mem_levelSubgroup_withP_iff D.sp.X' R.βX (R.datXt t) (R.levR F b) hκ
  refine ⟨hS.trans ?_, ?_⟩
  · constructor
    · rintro ⟨h1, h2⟩
      have hq := (rangeRestrict_mem_Q_iff D.sp.X' R.βX (R.datXt t) κ).2 h1
      exact ⟨hq, (hQ hq).symm ▸ (hH _).1 h2⟩
    · rintro ⟨hq, hp⟩
      exact ⟨(rangeRestrict_mem_Q_iff D.sp.X' R.βX (R.datXt t) κ).1 hq, (hH _).2 (hQ hq ▸ hp)⟩
  · intro hq hp
    have hP : rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ) ∈ (R.levR F b).H := (hH _).2 (hQ hq ▸ hp)
    refine (levelCharacter_withLevel_of_mem D.sp.X' R.βX (R.datXt t) hP).trans ?_
    refine (mul_comm _ _).trans (congrArg₂ (· * ·) (levChi_flagL_eq_ch _ _ _ hq) ?_)
    have e : (⟨_, hp⟩ : (F.lvl b).P) = ⟨R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)), (hH _).1 hP⟩ :=
      Subtype.ext (hQ hq)
    have key : (((R.levR F b).chi ⟨_, hP⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL (((F.lvl b).ψ ⟨R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)), (hH _).1 hP⟩ : D.what₂.LLˣ) : D.what₂.LL) :=
      rfl
    exact key.trans (congrArg (fun p => D.what₂.embLL (((F.lvl b).ψ p : D.what₂.LLˣ) : D.what₂.LL)) e.symm)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefLiftMult

open Matrix

theorem sig_of_posDef {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) := by
  obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
  have hq : q = 0 := by
    by_contra hq
    have j : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
    have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inr j)
    rw [hQ] at h1
    simp [Formalism.UG.Jpq] at h1
    exact absurd h1 (by norm_num)
  subst hq
  simp at hn
  rw [hn]

theorem exists_tauE (D : D7) (σ : D.host.E →+* ℂ) :
    ∃ τ, σ = tauE D τ ∨ σ = (starRingEnd ℂ).comp (tauE D τ) := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have key : ∀ (t : D.R.GG) (ht : t ∈ D.R.Psi),
      tauE D (D.eTau.symm ⟨t, ht⟩) = D.host.emb t := fun t ht => by
    unfold tauE
    rw [Equiv.apply_symm_apply]
  by_cases h : g ∈ D.R.Psi
  · exact ⟨D.eTau.symm ⟨_, h⟩, Or.inl (key g h).symm⟩
  · have h' : g * D.R.cc ∈ D.R.Psi := by
      by_contra h2
      exact h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h2)
    refine ⟨D.eTau.symm ⟨_, h'⟩, Or.inr ?_⟩
    rw [key, Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have := D.host.conjE_apply (D.host.emb g) x
    exact ((starRingEnd_self_apply _).symm.trans (congrArg (starRingEnd ℂ) this.symm))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem isDefinite (hs : V.SigOK) (h : AllPlus M) : V.IsDefinite := by
  intro σ
  refine Or.inl (sig_of_posDef ?_ (hs σ))
  obtain ⟨τ, rfl | rfl⟩ := exists_tauE D σ
  · exact h.posDef τ
  · have e : V.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D V τ)ᴴᵀ := by
      ext i j
      rfl
    rw [e]
    exact (h.posDef τ).conjTranspose.transpose

theorem rTr_mem {θ : InfFam D} (hθ : IsInfFam θ) (U : Set (GA D V → ℂ))
    (hU : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ U, rTr V (atTau θ V τ g) f ∈ U) {k : GA D V}
    (hk : k ∈ GinfC V) : ∀ f ∈ U, rTr V k f ∈ U := by
  classical
  obtain ⟨-, -, r3, -⟩ := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hu := GlobalTheory.RealLift.archM_mem hθ V k
  have e : GlobalTheory.RealLift.prodAt θ V Finset.univ.toList (fun τ => Formalism.L2.Pj.archM V (θ τ) k) = k :=
    r3 _ (GlobalTheory.RealLift.prodAt_mem θ V _ _) _ hk fun τ => by
      rw [GlobalTheory.RealLift.infMat_prodAt hθ V hu τ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
      rfl
  rw [← e]
  clear e
  generalize (Finset.univ.toList : List D.what₂.Tau) = l
  induction l with
  | nil =>
    intro f hf
    convert hf using 1
    funext g
    exact congrArg f (mul_one g)
  | cons τ l ih =>
    intro f hf
    convert hU τ _ (hu τ) _ (ih f hf) using 1
    funext g
    exact congrArg f (mul_assoc _ _ _).symm

open Classical in
theorem actT_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    inclT M (PiTensorProduct.tprod ℂ (Function.update v τ w)) = actT M τ g (inclT M (PiTensorProduct.tprod ℂ v)) := by
  unfold inclT actT
  simp only [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases c : ρ = τ
  · subst c
    simpa using hw
  · simp [Function.update_of_ne c]

theorem mem_multT_of_equivariant : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ) (L : SmT M →ₗ[ℂ] (GA D V → ℂ)), IsInfFam θ → V.SigOK → AllPlus M → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → FiniteDimensional ℂ (SmT M) → Function.Injective (inclT M) → IsTensAct M π → (∀ x, IsAutFun V (L x)) → (∀ x, ∀ k ∈ J, ∀ g, L x (g * k) = χ k * L x g) → (∀ τ u x, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x)) → L ∈ MultT θ M J χ := by
  intro D θ V S M π J χ L hθ hs hp hfd hT hinj hπ haut hlev heq
  have hd := isDefinite hs hp
  refine (mem_multT θ M J χ L).2 (Submodule.subset_span ?_)
  have e : ∀ v : M.Vec, PiTensorProduct.lift.symm L v = L (PiTensorProduct.tprod ℂ v) := fun v => rfl
  refine ⟨fun v => ?_, fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _, fun v k hk g => hlev _ k hk g,
    fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · rw [e]
    refine (GlobalTheory.DefiniteForms.autFunDefIffSm D θ hθ V hs hd _).1 ⟨haut _, ?_⟩
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, hk, rfl⟩
    refine rTr_mem hθ _ (fun τ g hg => ?_) hk _ (LinearMap.mem_range_self L _)
    rintro _ ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
    exact ⟨_, heq τ u x⟩
  · obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
    rw [e, e, ← heq]
    congr 1
    exact hinj ((actT_tprod τ _ v w hw).trans (hπ τ u _).symm)
  · haveI := (hfd τ).1
    exact GlobalTheory.DefiniteEnd.exists_sobCont M τ _ v x

end GlobalTheory.DefLiftMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveStrandComplementLefschetzStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_strand_complement_lefschetz : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (U : ℤ → Submodule ℂ V) (N : Module.End ℂ V) (m : ℕ), iSupIndep U → ⨆ i, U i = ⊤ → (∀ d, ∀ v ∈ U d, N v ∈ U (d + 2)) → (∀ i : ℕ, Set.BijOn (N ^ i) (U (-(i : ℤ))) (U i)) → (∀ k : ℤ, (m : ℤ) < k → U k = ⊥) → IsCompl (strand N (U (-(m : ℤ))) m) (lowPart U N m) := by
  first | exact @GlobalTheory.WeilDeligne.PrimDecomp.isCompl_strand_lowPart | exact GlobalTheory.WeilDeligne.PrimDecomp.isCompl_strand_lowPart | (intros; apply GlobalTheory.WeilDeligne.PrimDecomp.isCompl_strand_lowPart <;> assumption)
end

