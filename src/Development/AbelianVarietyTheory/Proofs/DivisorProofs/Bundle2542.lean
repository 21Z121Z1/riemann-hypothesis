import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueCompEndomorphisms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rosGen_comp_val : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}, GlobalFnsSt → IsAbelianScheme A → L.IsLB →
    ∀ (f₁ g₁ f₂ g₂ f g : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], f = f₂ ≫ f₁ → g = g₁ ≫ g₂ →
    ∀ (u₁ : LB.Gen (LB.LinComb L (rosatiφ A f₁ g₁) rosatiε)) (u₂ : LB.Gen (LB.LinComb L (rosatiφ A f₂ g₂) rosatiε))
      (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u₁.IsGen → u₂.IsGen → u.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₁ (zero2 A)) (LB.oneGen L) →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₂ (zero2 A)) (LB.oneGen L) →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) →
    ∀ {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → L.ι}, Good L z J → ∀ x y : T ⟶ A,
    val₂ u z J x y = val₂ u₁ z J (x ≫ f₂) y * val₂ u₂ z J x (y ≫ g₁) := by
  intro S A _ _ L hG hA hL f₁ g₁ f₂ g₂ f g _ _ _ _ hf hg u₁ u₂ u hu₁ hu₂ hu h₁ h₂ h₀ T z J hJ x y
  subst hf hg
  have zl : ∀ (a b : A ⟶ A) [IsMonHom a] [IsMonHom b], zero2 A ≫ (lift (fst A A ≫ a) (snd A A ≫ b)).left = zero2 A := by
    intro a b _ _
    show (lift η[A] η[A]).left ≫ _ = (lift η[A] η[A]).left
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  have v0 : ∀ {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
      (t : LB.Gen (LB.LinComb L φ ε)), LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t (zero2 A)) (LB.oneGen L) →
      ∀ {y : S} {I}, Good L y I → val t (zero2 A) y I = 1 := by
    intro K _ φ ε t ht y I hI
    have := val_corr hI ht (𝟙 _)
    rwa [val_pull hI, Category.id_comp, val_one] at this
  have key := gen_unique' hL (u := u)
    (u' := LB.mulGen L _ _ _ _ (LB.pullGen L _ _ u₁ (lift (fst A A ≫ f₂) (snd A A)).left)
      (LB.pullGen L _ _ u₂ (lift (fst A A) (snd A A ≫ g₁)).left))
    (fun V _ k => by
      have p := prod_ros (f₂ ≫ f₁) (g₁ ≫ g₂) (fst A A) (snd A A) k
      rw [lift_fst_snd, Over.id_left] at p
      simp only [Category.id_comp] at p
      refine (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
        (prod_ros f₁ g₁ (fst A A ≫ f₂) (snd A A) k) (prod_ros f₂ g₂ (fst A A) (snd A A ≫ g₁) k)).trans
        (Eq.trans ?_ p.symm)
      simp only [Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    ((snd A A).left ≫ A.hom) (zero2 A) (by
      rw [Over.w (snd A A)]; exact Over.w (lift η[A] η[A]))
    (surj_comp (surj_snd hG hA _) (hG _ _ hA).2) hu
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₁ _) (DVR.pullGen_isGen _ _ _ _ hu₂ _))
    (fun y I hI => by
      rw [v0 u h₀ hI, val_mul hI, val_pull hI, val_pull hI]
      have e1 := zl f₂ (𝟙 A)
      have e2 := zl (𝟙 A) g₁
      simp only [Category.comp_id] at e1 e2
      rw [e1, e2, v0 u₁ h₁ hI, v0 u₂ h₂ hI, _root_.mul_one])
    T.left (lift x y).left z J hJ
  unfold val₂
  rw [key, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift,
    lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLocalLevelCharacter
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

open scoped TensorProduct in
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.IndefR.principalLevelFrame in

theorem rowLocPin_congr {D : D7} {V : HSp D} {Sp : D.what₂.Tau → SPar} (lp : Formalism.L2.LPTiedPlaceholder D)
    {θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {PY PY' : principalLevelFrame.RowPsi V D.R.r}
    {M M' : Formalism.IndefR.Mult.DSModel V Sp} {J J' : Bool → Set (GA D V)} {χ χ' : Bool → GA D V → ℂ}
    {e e' : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} {eFT : D.what₂.FT ≃ principalLevelFrame.FTR θ PY M J χ e}
    {eFT' : D.what₂.FT ≃ principalLevelFrame.FTR θ' PY' M' J' χ' e'} (hθ : θ = θ') (hP : PY = PY') (hM : M = M') (hJ : J = J')
    (hχ : χ = χ') (he : e = e') (hE : HEq eFT eFT') (h : principalLevelFrame.RowLocPin lp θ PY M J χ e eFT) :
    principalLevelFrame.RowLocPin lp θ' PY' M' J' χ' e' eFT' := by
  subst hθ hP hM hJ hχ he
  cases hE
  exact h

set_option maxHeartbeats 4000000 in

theorem rowLocPin_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (lp : Formalism.L2.LPTiedPlaceholder (w.st Z).toD7)
    (hr : Formalism.IndefR.principalLevelFrame.RowLocPin lp t.r.z.R.θ t.r.Y.PY (t.r.z.R.MY 0)
      (fun s => levS _ (t.r.z.R.βY 0) (t.r.z.R.dat0 (t.r.z.R.toRealDat.levR t.r.z.F.lv2 s)))
      (fun s => Formalism.IndefR.Lev.levChi _ (t.r.z.R.βY 0) (t.r.z.R.dat0 (t.r.z.R.toRealDat.levR t.r.z.F.lv2 s)))
      (fun _ => t.r.z.R.e0) t.r.Y.eFT) :
    Formalism.IndefR.principalLevelFrame.RowLocPin lp a.x.R.θ a.x.Y.PY (a.x.R.MY 0)
      (fun s => levS _ (a.x.R.βY 0) (a.x.R.dat0 (a.x.R.toRealDat.levR a.x.F.lv2 s)))
      (fun s => Formalism.IndefR.Lev.levChi _ (a.x.R.βY 0) (a.x.R.dat0 (a.x.R.toRealDat.levR a.x.F.lv2 s)))
      (fun _ => a.x.R.e0) a.x.Y.eFT := by
  have hPY := a.PY
  have hE := a.eFT
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  dsimp only at hPY hE ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, Y, _⟩ := x
  dsimp only at pack hPY hE ⊢
  cases pack
  exact rowLocPin_congr lp rfl (eq_of_heq hPY).symm rfl rfl rfl rfl hE.symm hr

set_option maxHeartbeats 4000000 in

theorem rowLocPin_bwit : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b), q.O.L.sc = K.s → Formalism.IndefR.principalLevelFrame.RowLocPin b.R.T.n.gal.lp w.x.R.θ w.x.Y.PY (w.x.R.MY 0) (fun s => levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 s))) (fun s => Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 s))) (fun _ => w.x.R.e0) w.x.Y.eFT := by
  intro hL p
  apply GlobalTheory.Fc.EvP.of_all
  intro κ K _ q c b w _
  rw [show b.R.T.n.gal = q.core.a.all.gal from w.recPin.s.gal, ← eq_of_heq w.ax]
  exact rowLocPin_twArgs w.a _ q.core.row.rowLoc

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameGenericFibreChainRescaledDeeperRealisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SameChain

theorem spec_endo_eq_id {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (g : Sp Ω ⟶ Sp Ω)
    (h : g ≫ spMap R.val.toRingHom = spMap R.val.toRingHom) : g = 𝟙 _ := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have h2 : CommRingCat.ofHom R.val.toRingHom ≫ ψ = CommRingCat.ofHom R.val.toRingHom :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h)
  have e : ∀ c ∈ R, ψ.hom c = c := fun c hc => congrArg (fun f => f.hom (⟨c, hc⟩ : R)) h2
  have hψ : ψ = 𝟙 _ := by
    ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := frac x
    simp [map_div₀, e a ha, e b hb]
  rw [hψ, Spec.map_id]

theorem sec_of_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) {G : Over (Sp Ω)}
    (a : G.left ⟶ ρ.P.A.left) (h : IsPullback a G.hom ρ.P.A.hom (spMap S.R.val.toRingHom)) (w : Sp Ω ⟶ G.left)
    (x : S.Gam) (hw : w ≫ a = spMap S.R.val.toRingHom ≫ (ρ.pt x).left) : w ≫ G.hom = 𝟙 _ := by
  refine spec_endo_eq_id S.R S.frac _ ?_
  rw [Category.assoc, ← h.w, ← Category.assoc, hw, Category.assoc, Over.w (ρ.pt x)]
  simp

end GlobalTheory.Poinc.SameChain

open GlobalTheory.Poinc.SameChain in

theorem GlobalTheory.Poinc.same_chain_deep : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (D : Deep X₁ ε₁)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A))
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)),
  Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) →
  Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) := by
  intro g n F W Z i X₁ ε₁ D c₀ hc R' fg frac hth hev ρ' ε' c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ h1 h3
  obtain ⟨P₁, a₁, a₁', e₁, pa₁, pa₁', L₁, L₁', E₁, T₁⟩ := h1
  obtain ⟨P₀, b, b', e₀, pb, pb', L₀, L₀', E₀, T₀⟩ := D.same
  obtain ⟨P₃, c, c', e₃, pc, pc', L₃, L₃', E₃, T₃⟩ := h3
  have pa₁c : IsGrpPullback P₁.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a₁ := pa₁.congr (by rw [RingHom.id_comp]) rfl
  have pcc : IsGrpPullback P₃.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) c := pc.congr (by rw [RingHom.id_comp]) rfl
  have hspc := Geo.Tor.spMap_comp X₁.S.R.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)
  have pbc : IsGrpPullback P₀.A X₁.ρ.P.A (spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom) b :=
    pb.congr hspc rfl
  have wm : b ≫ X₁.ρ.P.A.hom = (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [pbc.1.w, Category.assoc]
  set m := pa₁c.1.lift b (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) wm with hmdef
  have hm1 : m ≫ a₁ = b := pa₁c.1.lift_fst _ _ wm
  have hm2 : m ≫ P₁.A.hom = P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁) := pa₁c.1.lift_snd _ _ wm
  have pm : IsGrpPullback P₀.A P₁.A (spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) m := pa₁c.cancel (pbc.congr rfl hm1.symm) hm2
  obtain ⟨e, he_mon, he⟩ := grpPullback_iso pb' pcc
  haveI := he_mon
  have pe := isGrpPullback_of_iso e
  refine ⟨P₀, m ≫ a₁', e.hom.left ≫ c', e₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pm.comp pa₁').congr (Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)).symm rfl
  · exact (pe.comp pc').congr (Category.id_comp _) rfl
  · have A : LBIso (X₁.ρ.P.L.pull b) (P₁.L.pull m) :=
      LBIso.chartPull (chartPullSame X₁.ρ.P.L (K := PUnit) (fun _ => b) (fun _ => a₁) (fun _ => 1) m
        (fun _ => hm1.symm)) (chartPullPull P₁.L m) L₁.symm
    have B : LBIso (P₁.L.pull m) (ρ'.P.L.pull (m ≫ a₁')) :=
      LBIso.chartPull (chartPullPull P₁.L m) (chartPullSame ρ'.P.L (K := PUnit) (fun _ => m ≫ a₁') (fun _ => a₁')
        (fun _ => 1) m (fun _ => rfl)) L₁'
    exact LBIso.trans P₀.isLB (pull_isLB P₁.isLB m) (pull_isLB ρ'.P.isLB _)
      (LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB b) (pull_isLB P₁.isLB m) L₀ A) B
  · have A : LBIso (D.X.ρ.P.L.pull b') (P₃.L.pull e.hom.left) :=
      LBIso.chartPull (chartPullSame D.X.ρ.P.L (K := PUnit) (fun _ => b') (fun _ => c) (fun _ => 1) e.hom.left
        (fun _ => he.symm)) (chartPullPull P₃.L e.hom.left) L₃.symm
    have B : LBIso (P₃.L.pull e.hom.left) (ρ₂.P.L.pull (e.hom.left ≫ c')) :=
      LBIso.chartPull (chartPullPull P₃.L e.hom.left) (chartPullSame ρ₂.P.L (K := PUnit)
        (fun _ => e.hom.left ≫ c') (fun _ => c') (fun _ => 1) e.hom.left (fun _ => rfl)) L₃'
    exact LBIso.trans P₀.isLB (pull_isLB P₃.isLB _) (pull_isLB ρ₂.P.isLB _)
      (LBIso.trans P₀.isLB (pull_isLB D.X.ρ.P.isLB b') (pull_isLB P₃.isLB _) L₀' A) B
  · intro E
    have k1 : (e₀ E).left ≫ m = m ≫ (e₁ E).left := by
      apply pa₁c.1.hom_ext
      · rw [Category.assoc, hm1, (E₀ E).1, Category.assoc, (E₁ E).1, ← Category.assoc, hm1]
      · rw [Category.assoc, hm2, ← Category.assoc, Over.w (e₀ E), Category.assoc, Over.w (e₁ E), hm2]
    have k3 : (e₀ E).left ≫ e.hom.left = e.hom.left ≫ (e₃ E).left := by
      apply pcc.1.hom_ext
      · rw [Category.assoc, he, (E₀ E).2, Category.assoc, (E₃ E).1, ← Category.assoc, he]
      · rw [Category.assoc, Over.w e.hom, Over.w (e₀ E), Category.assoc, Over.w (e₃ E), Over.w e.hom]
    refine ⟨?_, ?_⟩
    · rw [← Category.assoc, k1, Category.assoc, (E₁ E).2, Category.assoc]
    · rw [← Category.assoc, k3, Category.assoc, (E₃ E).2, Category.assoc]
  · intro x
    obtain ⟨w, hw, hw'⟩ := T₀ x
    obtain ⟨w₁, hw₁, hw₁'⟩ := T₁ x
    obtain ⟨w₃, hw₃, hw₃'⟩ := T₃ (D.lab x)
    have s0 : w ≫ P₀.A.hom = 𝟙 _ := sec_of_pt D.X.ρ b' pb'.1 w _ hw'
    have s1 : w₁ ≫ P₁.A.hom = 𝟙 _ := sec_of_pt ρ' a₁' pa₁'.1 w₁ _ hw₁'
    have s3 : w₃ ≫ P₃.A.hom = 𝟙 _ := sec_of_pt ρ₂ c' pc'.1 w₃ _ hw₃'
    have hwm : w ≫ m = spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ w₁ := by
      apply pa₁c.1.hom_ext
      · rw [Category.assoc, hm1, hw, Category.assoc, hw₁, hspc, Category.assoc, RingHom.id_comp]
      · rw [Category.assoc, hm2, ← Category.assoc, s0, Category.id_comp, Category.assoc, s1, Category.comp_id]
    have hwe : w ≫ e.hom.left = w₃ := by
      apply pcc.1.hom_ext
      · rw [Category.assoc, he, hw', hw₃, RingHom.id_comp]
      · rw [Category.assoc, Over.w e.hom, s0, s3]
    refine ⟨w, ?_, ?_⟩
    · rw [← Category.assoc, hwm, Category.assoc, hw₁', Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁),
        Category.assoc]
    · rw [← Category.assoc, hwe, hw₃']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameLineBundleFamilyDescendsFlatSurjectiveQuasiC
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem isPullback_prod_map {S : Scheme.{0}} (A : Over S) {V V' : Over S} (v : V ⟶ V') :
    IsPullback (lift (fst A V) (snd A V ≫ v)).left (snd A V).left (snd A V').left v.left := by
  have hT : IsPullback (fst A V).left (snd A V).left A.hom V.hom := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A V').left (snd A V').left A.hom V'.hom := IsPullback.of_hasPullback _ _
  have m₁ : (lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left = (fst A V).left := by
    rw [← Over.comp_left, lift_fst]
  have m₂ : (lift (fst A V) (snd A V ≫ v)).left ≫ (snd A V').left = (snd A V).left ≫ v.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hT' : IsPullback ((lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left) (snd A V).left A.hom
      (v.left ≫ V'.hom) := by
    rw [m₁, Over.w v]; exact hT
  exact IsPullback.of_right hT' m₂ hY

theorem isPullback_prod_kernel {S : Scheme.{0}} (A Y Y' W : Over S) (c : Y' ⟶ Y) (w₁ w₂ : W ⟶ Y')
    (hK : IsPullback w₁.left w₂.left c.left c.left) :
    IsPullback (lift (fst A W) (snd A W ≫ w₁)).left (lift (fst A W) (snd A W ≫ w₂)).left
      (lift (fst A Y') (snd A Y' ≫ c)).left (lift (fst A Y') (snd A Y' ≫ c)).left := by
  have Hc := isPullback_prod_map A c
  have H₂ := isPullback_prod_map A w₂
  have outer := H₂.flip.paste_horiz hK
  have e₁ : (lift (fst A W) (snd A W ≫ w₁)).left ≫ (snd A Y').left = (snd A W).left ≫ w₁.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have e₂ : (lift (fst A Y') (snd A Y' ≫ c)).left ≫ (snd A Y).left = (snd A Y').left ≫ c.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext hK.w
  refine IsPullback.of_right (h₁₂ := (snd A Y').left) (h₂₂ := (snd A Y).left) ?_ ?_ Hc.flip
  · rw [e₁, e₂]; exact outer
  · rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst, lift_fst, lift_snd_assoc,
      lift_snd_assoc, Category.assoc, Category.assoc, hw]

theorem same_of_fpqc : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (T U Y Y' : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → ∀ (y : Y ⟶ T) (u : Y ⟶ U) (c : Y' ⟶ Y), Flat c.left → Surjective c.left → QuasiCompact c.left → Same A N M (c ≫ y) (c ≫ u) → Same A N M y u := by
  intro S A _ hA T U Y Y' N M hN hM y u c hfl hsu hqc hc
  rw [same_iff hN.isLB hM.isLB, ← sub_eq_zero]
  obtain ⟨L, hL, hcl⟩ := cls_surj (evc hN.isLB (fst A Y) (snd A Y ≫ y) - evc hM.isLB (fst A Y) (snd A Y ≫ u))
  rw [← hcl]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ Y).left), Triv (L.pull f) ↔
      CechPic.pull f (evc hN.isLB (fst A Y) (snd A Y ≫ y)) = CechPic.pull f (evc hM.isLB (fst A Y) (snd A Y ≫ u)) := by
    intro X f
    rw [← sub_eq_zero, ← map_sub, ← hcl, ← cls_pull hL f (pull_isLB hL f)]
    exact (cls_eq_zero_iff (pull_isLB hL f)).symm
  refine (cls_eq_zero_iff hL).2 ?_
  let F : A ⊗ Y' ⟶ A ⊗ Y := lift (fst A Y') (snd A Y' ≫ c)
  let e : Y ⟶ A ⊗ Y := lift 1 (𝟙 Y)
  let e' : Y' ⟶ A ⊗ Y' := lift 1 (𝟙 Y')
  have h0 : Triv (L.pull e.left) := by
    rw [key]
    simp only [e, pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [hN.add.evc_one hN.isLB, hM.add.evc_one hM.isLB]
  have h1 : Triv (L.pull F.left) := by
    rw [key]
    simp only [F, pull_evc, lift_fst, lift_snd_assoc]
    rw [same_iff hN.isLB hM.isLB] at hc
    simpa only [Category.assoc] using hc
  have hEF : e' ≫ F = c ≫ e := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [e, e', F]
  have hep : e' ≫ snd A Y' = 𝟙 Y' := lift_snd _ _

  have hT : IsPullback (fst A Y').left (snd A Y').left A.hom Y'.hom := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback _ _
  have m₁ : F.left ≫ (fst A Y).left = (fst A Y').left := by rw [← Over.comp_left, lift_fst]
  have m₂ : F.left ≫ (snd A Y).left = (snd A Y').left ≫ c.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hT' : IsPullback (F.left ≫ (fst A Y).left) (snd A Y').left A.hom (c.left ≫ Y.hom) := by
    rw [m₁, Over.w c]; exact hT
  have H : IsPullback F.left (snd A Y').left (snd A Y).left c.left := IsPullback.of_right hT' m₂ hY
  have hF₁ : Flat F.left := MorphismProperty.of_isPullback H.flip hfl
  have hF₂ : Surjective F.left := MorphismProperty.of_isPullback H.flip hsu
  have hF₃ : QuasiCompact F.left := MorphismProperty.of_isPullback H.flip hqc

  let W : Over S := Over.mk (pullback.fst c.left c.left ≫ Y'.hom)
  let w₁ : W ⟶ Y' := Over.homMk (pullback.fst c.left c.left) rfl
  let w₂ : W ⟶ Y' := Over.homMk (pullback.snd c.left c.left) (by
    show pullback.snd c.left c.left ≫ Y'.hom = pullback.fst c.left c.left ≫ Y'.hom
    rw [← Over.w c, ← Category.assoc, ← pullback.condition, Category.assoc])
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext pullback.condition
  have hK : IsPullback w₁.left w₂.left c.left c.left := IsPullback.of_hasPullback c.left c.left
  let g₁ : A ⊗ W ⟶ A ⊗ Y' := lift (fst A W) (snd A W ≫ w₁)
  let g₂ : A ⊗ W ⟶ A ⊗ Y' := lift (fst A W) (snd A W ≫ w₂)
  have hKP : IsPullback g₁.left g₂.left F.left F.left := isPullback_prod_kernel A Y Y' W c w₁ w₂ hK
  have hg : g₁.left ≫ F.left = g₂.left ≫ F.left := hKP.w

  obtain ⟨g, hgg⟩ := h0
  obtain ⟨t, ht⟩ := h1
  have n₁ : (snd A Y' ≫ e').left ≫ F.left = (snd A Y' ≫ c).left ≫ e.left := by
    rw [← Over.comp_left, ← Over.comp_left, Category.assoc, hEF, Category.assoc]
  obtain ⟨t', ht', hv⟩ := exists_gen hL (K' := PUnit) (φ' := fun _ => F.left) (ε' := fun _ => 1)
    (fun U _ k => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, n₁]
      simp)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (snd A Y' ≫ e').left)))
      (LB.pullGen L _ _ g (snd A Y' ≫ c).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hgg _))
  have norm : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y'.left) (z : Z) (J), Geo.Tor.Good L z J →
      val t' (r ≫ e'.left) z J = val g (r ≫ c.left) z J := by
    intro Z r z J hJ
    have a₁ : (r ≫ e'.left) ≫ (snd A Y' ≫ e').left = r ≫ e'.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    have a₂ : (r ≫ e'.left) ≫ (snd A Y' ≫ c).left = r ≫ c.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    rw [hv Z _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, a₁, a₂, mul_inv_cancel,
      _root_.one_mul]
  refine GlobalTheory.T.lineBundle_trivial_of_generator_fpqc_descent L hL F.left hF₁ hF₂ hF₃ g₁.left g₂.left hKP t' ht' (fun z J hJ => ?_)
  let o : W ⟶ A ⊗ W := lift 1 (𝟙 W)
  have hg1 : o.left ≫ g₁.left = w₁.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₁, e']
  have hg2 : o.left ≫ g₂.left = w₂.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₂, e']
  have ho : o.left ≫ (snd A W).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have hwc : w₁.left ≫ c.left = w₂.left ≫ c.left := by rw [← Over.comp_left, ← Over.comp_left, hw]
  have key2 := gen_unique' hL (φ := fun _ : PUnit => g₁.left ≫ F.left) (ε := fun _ => (1 : ℤ))
    (φ' := fun _ : PUnit => g₂.left ≫ F.left) (ε' := fun _ => 1)
    (fun U _ k => by simp only [hg]) (snd A W).left o.left ho (surj_snd GlobalTheory.SemiRigid.globalFns hA W)
    (u := LB.pullGen L _ _ t' g₁.left) (u' := LB.pullGen L _ _ t' g₂.left)
    (DVR.pullGen_isGen _ _ _ _ ht' _) (DVR.pullGen_isGen _ _ _ _ ht' _)
    (fun y I hI => by rw [val_pull hI, val_pull hI, hg1, hg2, norm _ _ _ _ hI, norm _ _ _ _ hI, hwc])
    _ (𝟙 _) z J hJ
  rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at key2

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RescaleForm

open GlobalTheory.TauTwist (unitAt unitAt_injective IsScalarForm)

theorem scalar_of_laws {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O] (D : DegPre R)
    [inst : Module O D.X] (oa : D.OAct O) (w0 : O) (g : D.X → (FractionRing R)ˣ) (hB : D.TauBimult) (hW : TraceFormTwistIso D oa w0)
    (hB' : (GlobalTheory.PolDeg.rescale D g).TauBimult)
    (oa' : @DegPre.OAct R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst)
    (ho : @DegPre.OAct.onB R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' = oa.onB)
    (hW' : @TraceFormTwistIso R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' w0) :
    IsScalarForm O (fun a b => g (a + b) * (g a)⁻¹ * (g b)⁻¹) ∧
      ∀ y, g y = g (y + w0 • y) * (g y)⁻¹ * (g (w0 • y))⁻¹ := by
  letI : Module O (GlobalTheory.PolDeg.rescale D g).X := inst
  have hG := GlobalTheory.globalFns_holds
  let y : (TK R).left := IsLocalRing.closedPoint (FractionRing R)
  obtain ⟨I, hJ⟩ := GlobalTheory.DegPull.exists_good' D.P.isLB y
  have vt : ∀ a b, val ((GlobalTheory.PolDeg.rescale D g).tau a b) (𝟙 _) y I =
      unitAt (𝟙 (TK R).left) y (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * val (D.tau a b) (𝟙 _) y I := fun a b => by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact GlobalTheory.PolDeg.rescale_tau_val D g a b hJ
  have sy : ∀ a b, g (a + b) * (g a)⁻¹ * (g b)⁻¹ = g (b + a) * (g b)⁻¹ * (g a)⁻¹ := fun a b => by
    rw [add_comm, mul_right_comm]
  have al : ∀ a a' b, g (a + a' + b) * (g (a + a'))⁻¹ * (g b)⁻¹ =
      (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * (g (a' + b) * (g a')⁻¹ * (g b)⁻¹) := fun a a' b => by
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e' := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB' a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e'' := (congrArg₂ (· * ·) (vt (a + a') b).symm rfl).trans (e'.trans (congrArg₂ (· * ·) (vt a b) (vt a' b)))
    rw [_root_.mul_mul_mul_comm, ← e, _root_.mul_assoc, ← map_mul] at e''
    exact unitAt_injective y (mul_right_cancel e'')
  obtain ⟨onB', cl', tb'⟩ := oa'
  obtain rfl : onB' = oa.onB := ho
  refine ⟨⟨fun a b b' => ?_, sy, fun x a b => ?_⟩, fun a => ?_⟩
  · rw [sy, sy a b, sy a b']
    exact al b b' a
  · have hr := GlobalTheory.TorusExt.exists_isRos hG oa (star x)
    rw [star_star] at hr
    obtain ⟨u, hu, u₀⟩ := hr
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (oa.tau_bal x u hu u₀ a b) (𝟙 _))
    have e' := (val_mul hJ _ _ _).symm.trans (val_corr hJ (tb' x u hu u₀ a b) (𝟙 _))
    have e'' := (congrArg₂ (· * ·) (vt (x • a) b).symm rfl).trans (e'.trans (vt a (star x • b)))
    rw [← e, _root_.mul_assoc] at e''
    exact unitAt_injective y (mul_right_cancel e'')
  · obtain ⟨u, hu, u₀, h⟩ := hW
    obtain ⟨u', hu', u₀', h'⟩ := hW'
    have k := gen_unique' D.P.isLB (fun _ _ _ => rfl) D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu hu'
      (fun z J hz => by
        have a := val_corr hz u₀ (𝟙 _)
        have b := val_corr hz u₀' (𝟙 _)
        rw [val_pull hz, val_one, Category.id_comp] at a
        have b' := ((val_pull hz _ _ _).symm.trans b).trans (val_one _)
        rw [Category.id_comp] at b'
        exact a.trans b'.symm) _ (𝟙 _ ≫ D.xK a) y I hJ
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e' := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h' a) (𝟙 _)).trans (val_mul hJ _ _ _))
    rw [val_pull hJ] at e
    have e'' := (congrArg₂ (· * ·) (vt a (w0 • a)).symm (k.trans (val_pull hJ _ _ _).symm)).trans (e'.trans
      (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen (unitOn (g a)) (D.psi a) (𝟙 _) hJ) rfl))
    rw [_root_.mul_assoc, e] at e''
    exact (unitAt_injective y (mul_right_cancel (e''.trans (_root_.mul_assoc _ _ _)))).symm

theorem main : ∀ {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O] (D : DegPre R) [inst : Module O D.X] (oa : D.OAct O) (w0 : O) (g : D.X → (FractionRing R)ˣ), D.TauBimult → TraceFormTwistIso D oa w0 → (GlobalTheory.PolDeg.rescale D g).TauBimult → ∀ (oa' : @DegPre.OAct R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst), @DegPre.OAct.onB R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' = oa.onB → @TraceFormTwistIso R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' w0 → GlobalTheory.TauTwist.IsScalarForm O (fun a b => g (a + b) * (g a)⁻¹ * (g b)⁻¹) ∧ ∀ y, g y = g (y + w0 • y) * (g y)⁻¹ * (g (w0 • y))⁻¹ :=
  fun D _ oa w0 g a b c oa' d e => scalar_of_laws D oa w0 g a b c oa' d e

end GlobalTheory.RescaleForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfTranslatedThetaCoefficientProportional
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PsiRing

theorem secIsMul_of_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (g₁ g₂ : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ) (b₁ b₂ q : R), GlobalTheory.PsiRing.Coef D χ u th g₁ b₁ → GlobalTheory.PsiRing.Coef D χ u th g₂ b₂ → b₁ = q * b₂ → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q g₁ g₂ := by
  intro R _ _ D χ u th g₁ g₂ b₁ b₂ q h₁ h₂ hb
  refine GlobalTheory.IndivisibleSection.secIsMul_of_sval D.P.isLB fun y J hJ => ?_
  have e : lift (toUnit (𝟙_ _ ⊗ D.P.A)) (snd (𝟙_ _) D.P.A) = 𝟙 _ := by
    rw [toUnit_unique (toUnit _) (fst (𝟙_ _) D.P.A), lift_fst_snd]
  have e₁ := h₁ (𝟙_ _ ⊗ D.P.A) (snd _ _) y J hJ
  have e₂ := h₂ (𝟙_ _ ⊗ D.P.A) (snd _ _) y J hJ
  rw [e] at e₁ e₂
  refine e₁.trans (Eq.trans ?_ (congrArg (_ * ·) e₂.symm))
  rw [hb, GlobalTheory.IndivisibleSection.cst_mul', _root_.mul_assoc]

end GlobalTheory.PsiRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsPreimageAffineBaseChangeEqSumProductsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_preimage_affine_baseChange_eq_sum_products : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (P : Scheme.{0}) (p : P ⟶ Sp R) (V : P.Opens), IsAffineOpen V → ∀ x : Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ V), ∃ (n : ℕ) (a : Fin n → Γ(P, V)) (r : Fin n → R₁), x = ∑ i, ((pullback.fst p (spMap ρ)).app V).hom (a i) * ((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i)) := by
  first | exact @GlobalTheory.BaseChangeSpan.sections_preimage_affine_eq_sum | exact GlobalTheory.BaseChangeSpan.sections_preimage_affine_eq_sum | (intros; apply GlobalTheory.BaseChangeSpan.sections_preimage_affine_eq_sum <;> assumption)
end

