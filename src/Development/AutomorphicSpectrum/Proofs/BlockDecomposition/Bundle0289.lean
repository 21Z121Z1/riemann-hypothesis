import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0280
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorDifferentialRepresentative
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0281
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleTwistDifference
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

variable {X : Scheme.{0}}

theorem res_res_units {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (resG_resG h₁ h₂ _)

theorem mul_chart_cancel {S : Type} [CommRing S] (u G k' k u' a : S) (h : u = G * k' * u') (h' : k' * k = 1) :
    u * (k * a) = G * (u' * a) := by
  subst h
  linear_combination (G * u' * a) * h'

theorem eq_of_resG_near {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ y ∈ U, ∃ (W : X.Opens) (_ : y ∈ W) (hW : W ≤ U), resG X hW a = resG X hW b) : a = b :=
  ext_germ fun y hy => by
    obtain ⟨W, hyW, hW, e⟩ := h y hy
    rw [← germ_resG hW y hyW a, ← germ_resG hW y hyW b, e]

theorem iso_sec_chart {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (a : A.Sec) (p p' : B.ι) (q q' : A.ι)
    {W : X.Opens} (h₁ : W ≤ B.U p) (h₁' : W ≤ B.U p') (h₂ : W ≤ A.U q) (h₂' : W ≤ A.U q') :
    resG X (le_inf h₁ h₂) (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) * resG X h₂ (a.f q) =
      resG X (le_inf h₁ h₁') (B.g p p' : Γ(X, B.U p ⊓ B.U p')) *
        (resG X (le_inf h₁' h₂') (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q')) : Γ(X, B.U p' ⊓ A.U q')) *
          resG X h₂' (a.f q')) := by
  have hW : W ≤ (LB.div B A).U (p, q) ⊓ (LB.div B A).U (p', q') :=
    le_inf (le_inf h₁ h₂) (le_inf h₁' h₂')
  have e := congrArg (res hW) (hw (p, q) (p', q'))
  have e₂ : res hW ((LB.div B A).g (p, q) (p', q')) =
      res (le_inf h₁ h₁') (B.g p p') * (res (le_inf h₂ h₂') (A.g q q'))⁻¹ := by
    exact (map_mul (res hW) _ _).trans (congrArg₂ (· * ·) (res_res_units _ _ _)
      ((map_inv (res hW) _).trans (congrArg (·⁻¹) (res_res_units _ _ _))))
  rw [map_mul, e₂, res_res_units, res_res_units] at e
  have e₃ := congrArg (fun u : Γ(X, W)ˣ => (u : Γ(X, W))) e
  simp only [Units.val_mul] at e₃
  rw [sec_compat a q q' h₂ h₂']
  have e₄ : ((res (le_inf h₂ h₂') (A.g q q'))⁻¹ : Γ(X, W)ˣ).val * resG X (le_inf h₂ h₂') (A.g q q' : Γ(X, A.U q ⊓ A.U q')) = 1 :=
    Units.inv_mul (res (le_inf h₂ h₂') (A.g q q'))
  exact mul_chart_cancel _ _ _ _ _ _ e₃ e₄

theorem exists_secMaps {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : w.IsGen) (a : A.Sec) :
    ∃ b : B.Sec, SecMaps w a b := by
  have hself : ∀ (p : B.ι) {W : X.Opens} (h : W ≤ B.U p),
      resG X (le_inf h h) (B.g p p : Γ(X, B.U p ⊓ B.U p)) = 1 := by
    intro p W h
    have e := congrArg (fun u : Γ(X, B.U p)ˣ => resG X h (u : Γ(X, B.U p))) (hB.g_self p)
    simp only [val_res, resG_resG, Units.val_one, map_one] at e
    exact e
  have glue : ∀ p : B.ι, ∃ b : Γ(X, B.U p), ∀ q : A.ι, resG X (inf_le_left : B.U p ⊓ A.U q ≤ B.U p) b =
      (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) *
        resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q) := by
    intro p
    obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun q : A.ι => B.U p ⊓ A.U q) (B.U p)
      (fun _ => homOfLE inf_le_left)
      (fun y hy => by
        obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, A.U i by rw [hA.cover]; trivial)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, hq⟩)
      (fun q => (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) *
        resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q))
      (fun q q' => by
        have h₁ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ B.U p := inf_le_left.trans inf_le_left
        have h₂ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ A.U q := inf_le_left.trans inf_le_right
        have h₃ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ A.U q' := inf_le_right.trans inf_le_right
        have k := iso_sec_chart hw a p p q q' h₁ h₁ h₂ h₃
        rw [hself p h₁, one_mul] at k
        change resG X inf_le_left _ = resG X inf_le_right _
        rw [map_mul, map_mul]
        repeat rw [resG_resG]
        exact k)
    exact ⟨b, hb⟩
  choose b hb using glue
  refine ⟨⟨b, fun p p' => ?_⟩, fun r => hb r.1 r.2⟩
  refine eq_of_resG_near fun y hy => ?_
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, A.U i by rw [hA.cover]; trivial)
  have h₀ : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p ⊓ B.U p' := inf_le_left
  have h₁ : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p := inf_le_left.trans inf_le_left
  have h₁' : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p' := inf_le_left.trans inf_le_right
  have h₂ : B.U p ⊓ B.U p' ⊓ A.U q ≤ A.U q := inf_le_right
  refine ⟨B.U p ⊓ B.U p' ⊓ A.U q, ⟨hy, hq⟩, h₀, ?_⟩
  have e₁ := congrArg (resG X (le_inf h₁ h₂)) (hb p q)
  have e₂ := congrArg (resG X (le_inf h₁' h₂)) (hb p' q)
  rw [map_mul, resG_resG, resG_resG] at e₁ e₂
  have k := iso_sec_chart hw a p p' q q h₁ h₁' h₂ h₂
  change resG X h₀ (resG X inf_le_left (b p)) = resG X h₀ ((B.g p p' : Γ(X, B.U p ⊓ B.U p')) * resG X inf_le_right (b p'))
  rw [map_mul, resG_resG, resG_resG]
  exact e₁.trans (k.trans (congrArg _ e₂.symm))

theorem relAmple_tw_of_roots : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (m : ℕ) (ζ : Fin (m + 1) → LB.Sec Q), Q.IsLB → VeryAmpleBy X.hom Q ζ → ∀ (A C : LB X.left) (n : ℕ), 1 ≤ n → A.IsLB → C.IsLB → LBIso (pw A ((n + 1 : ℕ) : ℤ)) Q → LBIso (pw C (n : ℤ)) Q → RelAmple X (tw C A (-1)) := by
  intro R _ X Q m ζ hQ hva A C n hn hA hC hAQ hCQ
  have hM : (tw C A (-1)).IsLB := isLB_tw hC hA _
  have hD : 1 ≤ n * (n + 1) := Nat.mul_pos hn (Nat.succ_pos n)
  have hP := isLB_pw hM ((n * (n + 1) : ℕ) : ℤ)
  have hcls : GlobalTheory.CechPic.cls _ hP = GlobalTheory.CechPic.cls Q hQ := by
    have hc : GlobalTheory.CechPic.cls _ hM = GlobalTheory.CechPic.cls C hC - GlobalTheory.CechPic.cls A hA := by
      refine (GlobalTheory.CechPic.cls_div hC (isLB_pw hA _) hM).trans ?_
      rw [GlobalTheory.AmpleStabFinite.cls_pw hA]
      simp
    have e₁ : ((n + 1 : ℕ) : ℤ) • GlobalTheory.CechPic.cls A hA = GlobalTheory.CechPic.cls Q hQ :=
      (GlobalTheory.AmpleStabFinite.cls_pw hA _).symm.trans ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hAQ)
    have e₂ : (n : ℤ) • GlobalTheory.CechPic.cls C hC = GlobalTheory.CechPic.cls Q hQ :=
      (GlobalTheory.AmpleStabFinite.cls_pw hC _).symm.trans ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hCQ)
    rw [GlobalTheory.AmpleStabFinite.cls_pw hM, hc, smul_sub]
    have f₁ : ((n * (n + 1) : ℕ) : ℤ) • GlobalTheory.CechPic.cls C hC = ((n + 1 : ℕ) : ℤ) • GlobalTheory.CechPic.cls Q hQ := by
      rw [← e₂, smul_smul]; congr 1 <;> (push_cast; ring)
    have f₂ : ((n * (n + 1) : ℕ) : ℤ) • GlobalTheory.CechPic.cls A hA = (n : ℤ) • GlobalTheory.CechPic.cls Q hQ := by
      rw [← e₁, smul_smul]; congr 1 <;> (push_cast; ring)
    rw [f₁, f₂, ← sub_smul]
    simp
  obtain ⟨w, hw⟩ : LBIso Q (pw (tw C A (-1)) ((n * (n + 1) : ℕ) : ℤ)) := (GlobalTheory.CechPic.cls_eq_iff hQ hP).1 hcls.symm
  choose t ht using fun i => exists_secMaps hQ hP hw (ζ i)
  obtain ⟨hs, hci⟩ := (veryAmpleBy_iff X.hom ζ).1 hva
  have ht' := iSup_nonzeroLocus_of_secMaps hs hQ hP ht
  refine GlobalTheory.Unif.relAmple_of_veryAmpleBy hM hD t ((veryAmpleBy_iff X.hom t).2 ⟨ht', ?_⟩)
  rw [toProj_eq_of_secMaps hs ht' ht]
  exact hci

end GlobalTheory.CompanionTheory.FormalAlg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePull
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.BetaRed

universe w₁ w₂ w₃ w₄ u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

theorem square_pull {R : Type} [CommRing R] {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{w₁} R} {F₂ : C₂ ⥤ ModuleCat.{w₂} R} {F₃ : C₃ ⥤ ModuleCat.{w₃} R} {F₄ : C₄ ⥤ ModuleCat.{w₄} R}
    (a : CH.Mor F₁ F₂ (RingHom.id R)) (b : CH.Mor F₂ F₄ (RingHom.id R))
    (c : CH.Mor F₁ F₃ (RingHom.id R)) (d : CH.Mor F₃ F₄ (RingHom.id R))
    (η : d.G ⋙ c.G ⟶ b.G ⋙ a.G)
    (hτ : ∀ T x, b.τ T (a.τ (b.G.obj T) ((F₁.map (η.app T)).hom x)) = d.τ T (c.τ (d.G.obj T) x))
    (j : ℕ) (x : CH.H F₁ j) : b.pull j (a.pull j x) = d.pull j (c.pull j x) := by
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) a b j x).1, ← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) c d j x).1]
  exact (CrystallineSemistableComparison.P.prism (c.comp d) (a.comp b) η hτ j x).symm

theorem map_map_eq (P : CommRingCat.{0} ⥤ Type) {A B D : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ D)
    (h : f ≫ g = f') (y : P.obj A) : P.map g (P.map f y) = P.map f' y := by
  subst h
  rw [Functor.map_comp_apply]

variable {l : ℕ} [Fact l.Prime]

theorem uJ_red (k : Bool) (A : PAlg l) {m n : ℕ} (h : n ≤ m) (e) :
    (Ideal.quotientMap (JJ k A n) (A.red h) e).comp (uJ k A m) = uJ k A n := RingHom.ext fun x => by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

abbrev redCr (k : Bool) {m n : ℕ} (h : n ≤ m) :
    GlobalTheory.LogCris.Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl (dd_red k _ h)
    (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

def redTh (k : Bool) {m n : ℕ} (h : n ≤ m) (T : (F.pt κ).Elements) :
    gObj F κ k m T ⟶ (redCr F κ k h).obj (gObj F κ k n T) :=
  crHom (T := gObj F κ k m T) (T' := (redCr F κ k h).obj (gObj F κ k n T)) (T.1.red h)
    (fun r => (pdOk_hom T.1.fromBase).red_acr h r) (dd_red k T.1 h) fun e => by
      exact map_map_eq F.Pt (CommRingCat.ofHom (uJ k T.1 m)) (CommRingCat.ofHom (Ideal.quotientMap (JJ k T.1 n) (T.1.red h) e))
        (CommRingCat.ofHom (uJ k T.1 n)) (CommRingCat.hom_ext (uJ_red k T.1 h e)) T.2.1

def redNat (k : Bool) {m n : ℕ} (h : n ≤ m) :
    (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).G ⋙ (βMor F κ k m).G ⟶ (βMor F κ k n).G ⋙ (redMor F κ k h).G where
  app T := redTh F κ k h ((jE (F.pt κ)).obj T)
  naturality T T' f := Thick.Hom.ext (RingHom.ext fun x => (pdOk_hom f.1.hom).red_acr h x) (funext fun j => j.elim)

theorem beta_red (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j) :
    β F κ k n j (redHc F κ k h j x) = (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).pull j (β F κ k m j x) :=
  square_pull (redMor F κ k h) (βMor F κ k n) (βMor F κ k m) (CH.Mor.ofNatTrans (redEl (F.pt κ) h))
    (redNat F κ k h) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.BetaRed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePullBijectiveOfAcyclic
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LengthOneCochainExactness

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

noncomputable def incl (b : IdF A) : CH.Mor (sq b (IdF.bot A)) (CH.modF A) (RingHom.id R) where
  G := 𝟭 C
  τ T := (AlgEquiv.quotientBot R (A.obj T)).toLinearMap ∘ₗ (sqM b (IdF.bot A) T).subtype
  nat φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

theorem incl_mem (b : IdF A) {T : C} (x : (sq b (IdF.bot A)).obj T) : (incl b).τ T x ∈ b.S T := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact hy

theorem cochain_exact (a b : IdF A) (ha : ∀ T, a.S T = ⊤) :
    (∀ n, Function.Injective ((incl b).hom.f n)) ∧
    (∀ n, Function.Exact ((incl b).hom.f n) ((toSq a b ha).hom.f n)) ∧
    ∀ n, Function.Surjective ((toSq a b ha).hom.f n) := by
  refine ⟨fun n x y hxy => ?_, fun n y => ⟨fun hy => ?_, ?_⟩, fun n y => ?_⟩
  · funext s
    have h : (incl b).τ _ (x (s ⋙ 𝟭 C)) = (incl b).τ _ (y (s ⋙ 𝟭 C)) := congrFun hxy s
    exact Subtype.ext ((AlgEquiv.quotientBot R _).injective h)
  · have hm : ∀ s : ComposableArrows C n,
        (show A.obj (s.obj (Fin.last n)) from y s) ∈ b.S (s.obj (Fin.last n)) := fun s => by
      have h := congrArg Subtype.val (congrFun hy s)
      exact Ideal.Quotient.eq_zero_iff_mem.1 h
    exact ⟨fun s => sqMk b (IdF.bot A) _ (hm s), rfl⟩
  · rintro ⟨x, rfl⟩
    funext s
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (incl_mem b (x (s ⋙ 𝟭 C))))
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)),
        Ideal.Quotient.mk _ t = (show sqM a b _ from y s).1 :=
      fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

theorem pull_toSq_bijective (a b : IdF A) (ha : ∀ T, a.S T = ⊤) :
    (∀ j, Subsingleton (CH.H (sq b (IdF.bot A)) j)) →
      ∀ j, Function.Bijective ((toSq a b ha).pull j) := by
  intro hv j
  obtain ⟨hf, hfg, hg⟩ := cochain_exact a b ha
  obtain ⟨δ, -, -, hex, hex2, -⟩ := CrystallineSemistableComparison.P.les _ _ hf hfg hg
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hex j x).1 hx
    rw [(hv j).elim y 0, map_zero]
  · intro y
    obtain ⟨x, hx⟩ := (hex2 j y).1 ((hv (j + 1)).elim _ _)
    exact ⟨x, hx⟩

end GlobalTheory.CompanionTheory.LengthOneCochainExactness
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrongApproxClosureMulStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approx_closure_mul : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (s : Pl F), ∀ x ∈ closure (SAQ d β s), ∀ y ∈ closure (SAQ d β s),
  x * y ∈ closure (SAQ d β s) := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.closure_SAQ_mul | exact GlobalTheory.CompanionTheory.PlaneSA.closure_SAQ_mul | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.closure_SAQ_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X : Scheme.{0}}

def secMulOn {N : LB X} {a b c : ℤ} (h : a + b = c) {V : X.Opens} (x : SecOn (pw N a) V)
    (y : SecOn (pw N b) V) : SecOn (pw N c) V :=
  GlobalTheory.LB.mkSec (L := pw N c) (fun i => @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (GlobalTheory.LB.coord x i) (GlobalTheory.LB.coord y i)) (fun i j => by
    have hx := GlobalTheory.LB.coord_rel x i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    have hy := GlobalTheory.LB.coord_rel y i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    subst h
    have e : ((N.g i j ^ (a + b) : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) =
        ((N.g i j ^ a : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) *
          ((N.g i j ^ b : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) := by
      rw [zpow_add, Units.val_mul]
    erw [map_mul, map_mul]
    erw [hx, hy, e, map_mul]
    rw [show (AbLaw.pw N a).g i j = N.g i j ^ a from rfl, show (AbLaw.pw N b).g i j = N.g i j ^ b from rfl]
    exact mul_mul_mul_comm _ _ _ _)

@[simp] theorem coord_secMulOn {N : LB X} {a b c : ℤ} (h : a + b = c) {V : X.Opens}
    (x : SecOn (pw N a) V) (y : SecOn (pw N b) V) (i : N.ι) :
    GlobalTheory.LB.coord (secMulOn h x y) i =
      @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (GlobalTheory.LB.coord x i) (GlobalTheory.LB.coord y i) := rfl

end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X : Scheme.{0}} {R : Type} [CommRing R]

def mulRight (f : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {a b c : ℤ} (h : a + b = c)
    {V : X.Opens} (y : SecOn (pw N b) V) : SecOnR f (pw N a) V →ₗ[R] SecOnR f (pw N c) V where
  toFun x := SecOnR.of f _ V (secMulOn h ((SecOnR.of f _ V).symm x) y)
  map_add' x x' := GlobalTheory.LB.sec_ext fun (i : N.ι) => add_mul (R := Γ(X, V ⊓ N.U i)) _ _ _
  map_smul' r x := GlobalTheory.LB.sec_ext fun (i : N.ι) => mul_assoc (G := Γ(X, V ⊓ N.U i)) _ _ _

theorem coord_mulRight (f : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {a b c : ℤ} (h : a + b = c)
    {V : X.Opens} (y : SecOn (pw N b) V) (x : SecOnR f (pw N a) V) (i : N.ι) :
    SecOnR.coord (mulRight f h y x) i =
      @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (SecOnR.coord x i) (GlobalTheory.LB.coord y i) :=
  rfl

def oneOn (N : LB X) {a : ℤ} (h : a = 0) (V : X.Opens) : SecOn (pw N a) V :=
  GlobalTheory.LB.mkSec (L := pw N a) (fun _ => 1) (fun i j => by
    subst h
    rw [map_one, map_one, show (AbLaw.pw N 0).g i j = N.g i j ^ (0 : ℤ) from rfl, zpow_zero,
      Units.val_one]
    erw [map_one, one_mul])

section Tower

variable (I : Ideal R)

abbrev toR (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) :
    (Y e).left ⟶ Spec (CommRingCat.of R) :=
  (Y e).hom ≫ thick R I e

theorem toR_w (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (e : ℕ) :
    β e ≫ toR I Y (e + 1) =
      toR I Y e ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, toR, toR, ← Category.assoc, (hβ e).w,
    Category.assoc, thickTrans_comp]

variable {ι : Type} (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (N : ∀ e, LB (Y e).left) (D : ∀ e, Finset ι → (Y e).left.Opens) (d : ℤ)

abbrev Tm (e : ℕ) (t : ℤ) (S : Finset ι) : Type :=
  SecOnR (toR I Y e) (pw (N e) (d * t)) (D e S)

def resT (hD : ∀ e (S S' : Finset ι), S ⊆ S' → D e S' ≤ D e S) (e : ℕ) (t : ℤ) {S S' : Finset ι}
    (h : S ⊆ S') : Tm I Y N D d e t S →ₗ[R] Tm I Y N D d e t S' :=
  SecOnR.restrict (toR I Y e) _ (hD e S S' h)

def mulT (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) :
    Tm I Y N D d e t S →ₗ[R] Tm I Y N D d e (t + 1) S :=
  mulRight (toR I Y e) (by ring) σ

theorem mulT_comm (e : ℕ) (t : ℤ) (S : Finset ι) (σ τ : SecOn (pw (N e) d) (D e S))
    (x : Tm I Y N D d e t S) :
    mulT I Y N D d e (t + 1) S σ (mulT I Y N D d e t S τ x) =
      mulT I Y N D d e (t + 1) S τ (mulT I Y N D d e t S σ x) := by
  refine SecOnR.ext_iff.mpr fun i => ?_
  unfold mulT
  first
  | (erw [coord_mulRight, coord_mulRight, coord_mulRight, coord_mulRight]; exact mul_right_comm _ _ _)
  | (simp only [coord_mulRight]; exact mul_right_comm _ _ _)
  | (simp only [coord_mulRight]; ring)

def oneT (e : ℕ) (S : Finset ι) : Tm I Y N D d e 0 S :=
  SecOnR.of _ _ _ (oneOn (N e) (mul_zero d) (D e S))

def redL (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens)
    (V' : (Y e).left.Opens) (h : V' ≤ β e ⁻¹ᵁ V) :
    SecOnR (toR I Y (e + 1)) (L (e + 1)) V →ₗ[R] SecOnR (toR I Y e) (L e) V' :=
  (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 V')).symm.toLinearMap ∘ₗ SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V V' h

def red (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e)))
    (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen)
    (hDβ : ∀ e (S : Finset ι), D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (e : ℕ) (S : Finset ι) :
    SecOnR (toR I Y (e + 1)) (pw (N (e + 1)) a) (D (e + 1) S) →ₗ[R]
      SecOnR (toR I Y e) (pw (N e) a) (D e S) :=
  redL I Y β hβ (fun e => pw (N e) a) (fun e => pullPow (v e) a)
    (fun e => ⟨isLB_pw (hN e).1 a, pullPow_isGen (v e) a (hN e).2⟩) e (D (e + 1) S) (D e S) (hDβ e S)

end Tower

section Sub

variable {ι : Type} [DecidableEq ι]

theorem sub_pair_left (i j : ι) : ({i} : Finset ι) ⊆ {i, j} :=
  Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)

theorem sub_pair_right (i j : ι) : ({j} : Finset ι) ⊆ {i, j} :=
  Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem sub_triple_ij (i j k : ι) : ({i, j} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem sub_triple_jk (i j k : ι) : ({j, k} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem sub_triple_ik (i j k : ι) : ({i, k} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

end Sub

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeOfAffineCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subobject_le_of_affine_cover : ∀ {X : Scheme.{0}} {E : X.Modules} [E.IsQuasicoherent] (S T : Subobject E), (S : X.Modules).IsQuasicoherent → (T : X.Modules).IsQuasicoherent → ∀ {ι : Type} (V : ι → X.Opens), (∀ i, IsAffineOpen (V i)) → iSup V = ⊤ → (∀ i, secs S (V i) ⊆ secs T (V i)) → S ≤ T := by
  first | exact @GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover | exact GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover | (intros; apply GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportProductOverPlacesStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_product_over_places : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (N : Set (Q d β (AF F))), (1 : Q d β (AF F)) ∈ N →
  (∀ x ∈ N, ∀ y ∈ N, x * y ∈ N) → (∀ u : Pl F, SuppAt d β {u} ⊆ N) →
  ∀ T : Finset (Pl F), SuppAt d β (T : Set (Pl F)) ⊆ N := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places | exact GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorDifferentialRepresentativeStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_differential_representative : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D), Taylor Fil E p → ∀ (n : ℕ) (f : CH.Cn (CH.modF Φ.A) n) (y : Idx n d → Φ.A.obj E.D) (c : CH.H (gr Fil (n : ℤ)) n)
      (x : CH.H (gr Fil ((n : ℤ) + 1)) (n + 1)),
      CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => f u) c →
      CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => ∑ I : Idx n d, E.form σ I.1 (y I) u) c →
      CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) (fun u => CH.d _ n f u) x →
      CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1))
        (fun u => ∑ a : Idx n d × Fin d, E.form σ (Fin.snoc (α := fun _ => Fin d) a.1.1 a.2) ((-1) ^ n * p a.2 (y a.1)) u) x := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.connecting_form | exact GlobalTheory.CompanionTheory.ConeLocal.connecting_form | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.connecting_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrameStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_of_local_frame : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε →
    letI := (strV q W).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, W) Γ(X, W)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    Taylor (sFil (KS q s {W})) E (fun k x => ε (D k (ε.symm x))) := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.taylor_loc | exact GlobalTheory.CompanionTheory.ConeLocal.taylor_loc | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.taylor_loc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFieldOrSplitIdempotentStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_field_or_split_idempotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) ∨ ∃ e : K ⊗[F] E, e * e = e ∧ e + sigR K σ e = 1 ∧ e * sigR K σ e = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.Dichotomy.field_or_split | exact GlobalTheory.CompanionTheory.SaGen.Dichotomy.field_or_split | (intros; apply GlobalTheory.CompanionTheory.SaGen.Dichotomy.field_or_split <;> assumption)
end

