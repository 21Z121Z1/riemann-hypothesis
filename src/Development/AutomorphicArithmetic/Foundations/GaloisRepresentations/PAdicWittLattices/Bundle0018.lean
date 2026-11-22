import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

open GlobalTheory.UPel.HT.Hecke in

private theorem gObjMap_comp_keep {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) :
    ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have e₁ : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have e₂ : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ => h₂.φ₂) (fun _ => 1) h₁.φ₂) e₁
  refine ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, ?_, ?_,
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol e₂, ?_⟩, rfl⟩
  · exact ⟨by simp only [Category.assoc, h₂.sq.1, reassoc_of% h₁.sq.1],
      by simp only [Category.assoc, h₂.sq.2, reassoc_of% h₁.sq.2]⟩
  · intro c
    simp only [← Category.assoc, h₁.act c]
    simp only [Category.assoc, h₂.act c]
  · intro y
    simp only [reassoc_of% h₁.eta y, h₂.eta y, Category.assoc]

theorem UpperTheory.Gal.G3.pWitEx :
    KNBasic → GenSm → Rigid → WitForget → WitDeep → DescMap → TransIso → TransCancel → TransDesc → WitEx := by
  intro _ hSm hRig hWF hWD hDM hTI hTC hTD p _ D G L R _ _ gb X N' N h hI hA
  obtain ⟨M, hdiv, hAM, π₁, Φ₁, hs₁, o₁, ψ₁, φ₁, ht₁, hΦ₁⟩ := hWD p D G L R gb X N' N h hI
  obtain ⟨c, Φc, hw, hfin, het, hsur⟩ := hWF p D G L R gb N' M hdiv (X N') (X M)
  have hA1 : AdmK L (↑M) (↑N') 1 := by
    intro u hu
    simpa using UpperTheory.Gal.Int.Geo.KN_anti hdiv hu
  obtain ⟨π, Φ, hcπ, hΦ, hπs, hΦw⟩ :=
    hDM p D G L R gb M N' N (X M) (X N') (X N) h hI hA hA1 c Φc π₁ Φ₁ hw hfin het hsur
      ⟨hs₁, o₁, ψ₁, φ₁, ht₁, hΦ₁⟩
  subst hcπ
  obtain ⟨hsc, oc, ψc, φc, htc, hΦc⟩ := hw
  obtain ⟨o, ⟨φ⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (X N').s π hπs (X N).univ
  let ψl : (X N').univ.A.left ⟶ o.A.left :=
    φ.cart.1.lift Φ (X N').univ.A.hom hΦw
  have hψ₁ : ψl ≫ φ.φ = Φ := φ.cart.1.lift_fst _ _ _
  have hψ₂ : ψl ≫ o.A.hom = (X N').univ.A.hom := φ.cart.1.lift_snd _ _ _
  let ψ : (X N').univ.A ⟶ o.A := Over.homMk ψl hψ₂
  refine ⟨π, Φ, hπs, o, ψ, φ, ?_, hψ₁.symm⟩
  obtain ⟨m₂⟩ := BaseChange.gObjMap_cancel φ₁ φ
  haveI := hTI p D G L R gb (X M).X (X M).s M N' (X M).univ oc ψc 1 (one_mem _) htc
  have htr : IsTrans L h oc o₁ (inv ψc ≫ ψ₁) :=
    hTC p D G L R gb (X M).X (X M).s M N' N (X M).univ oc o₁ ψc (inv ψc ≫ ψ₁) h hI hAM htc
      (by simpa using ht₁)
  haveI : Smooth (X M).s := (hSm p D R gb M (X M)).1
  haveI : AlgebraicGeometry.IsReduced (X M).X := GlobalTheory.isReduced_of_smooth_of_isReduced (X M).s
  have hcomp : m₂.φ ≫ φ.φ = φ₁.φ := by
    obtain ⟨m, hm⟩ := gObjMap_comp_keep m₂ φ
    rw [← hm]
    exact hRig p D R gb (X N).X (X M).X (X N).s (X M).s (c ≫ π)
      (by rw [Category.assoc, hπs, hsc]) N (X N).univ o₁ m φ₁
  refine hTD p D G L R gb (X N').X (X M).X (X N').s (X M).s c hsc N' N (X N').univ o oc o₁ φc m₂ ψ
    (inv ψc ≫ ψ₁) h ?_ htr
  have key : ψc.left ≫ φc.φ ≫ Φ = ψ₁.left ≫ φ₁.φ := by
    rw [← Category.assoc, ← hΦc, hΦ, hΦ₁]
  apply φ.cart.1.hom_ext
  · simp only [Category.assoc, hcomp, ψ, Over.homMk_left, hψ₁, Over.comp_left]
    rw [← key, ← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left, Category.id_comp]
  · simp only [Category.assoc, ψ, Over.homMk_left, hψ₂, Over.comp_left]
    rw [m₂.cart.1.w, φc.cart.1.w, ← Over.comp_left_assoc, Over.w_assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem kn_le_one {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (N : ℕ) {g : G.GAf}
    (hg : g ∈ L.KN N) : g ∈ L.KN 1 := by
  have key : ∀ {a : G.GAf}, L.CongOne N a → L.CongOne 1 a := by
    intro a ha v hv
    obtain ⟨w, hw, e⟩ := ha v hv
    exact ⟨N • w, nsmul_mem hw N, by rw [e, one_smul]⟩
  exact ⟨key hg.1, key hg.2⟩

theorem UpperTheory.Gal.G3.pWitFree :
    KNBasic → TransComp → TransPull → TransOfMap → TransFree → PtEq → WitCart → WitEx → WitFree := by
  intro hKN hComp hPull hOfMap hFree hPt hCart hEx
  intro p _ D G L R _ _ gb X N' N hle u hu π Φ hW k _ _ x hx
  have hu1 : u ∈ L.KN 1 := kn_le_one L N hu
  have hI1 : Integ L (1 : G.GAf) := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
  have hA1 : AdmK L (↑N') (↑N) (1 : G.GAf) := by
    intro v hv
    simpa using hle hv
  have hA0 : AdmK L (↑N') (↑N') (1 : G.GAf) := (hKN p D G L N').1 1 (one_mem _)
  obtain ⟨π₁, Φ₁, hW1⟩ := hEx p D G L R gb X N' N 1 hI1 hA1
  have hpb1 := hCart p D G L R gb _ _ (X N') (X N) 1 (one_mem _) π₁ Φ₁ hW1
  obtain ⟨_, o, ψ, φ, hψ, _⟩ := hW
  obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ (X N').s) x rfl (X N').univ
  obtain ⟨oo, ⟨m2⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ (X N').s) x rfl o
  obtain ⟨ψ', hψ', _⟩ := hPull p D G L R gb _ _ _ _ x rfl _ _ (X N').univ o ox oo mx m2 ψ u hψ
  have hn1 : Nonempty (GObjMap oo (X N').univ (𝟙 _ ≫ x)) := by
    have h := Unique.gObjMap_comp m2 φ
    have e : x ≫ π = 𝟙 _ ≫ x := by rw [hx, Category.id_comp]
    rwa [e] at h
  obtain ⟨mm⟩ := hn1
  obtain ⟨n⟩ := BaseChange.gObjMap_cancel mm mx
  obtain ⟨θ, _, hθ⟩ := hOfMap p D G L R gb _ _ N' oo ox n
  have hα := hComp p D G L R gb _ _ _ N' N' ox oo ox ψ' θ u 1 hI1 hA0 hψ' hθ
  rw [_root_.one_mul] at hα
  have hpt := (hPt p D G L R gb N' N' N (X N') (X N') (X N) 1 1 u u⁻¹ π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI1 hI1
    hA1 hA1 (inv_mem hu) (by rw [_root_.one_mul, inv_mul_cancel]) k (x ≫ (X N').s) x x rfl rfl
    ox ox mx mx (ψ' ≫ θ) hα).2
  have hpb := IsPullback.paste_horiz mx.cart.1 hpb1
  have hid : ψ' ≫ θ = 𝟙 ox.A := by
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · simpa [Category.assoc] using hpt.symm
    · simp
  rw [hid] at hα
  exact hFree p D G L R gb k (x ≫ (X N').s) N' ox u hu1 hα
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitOne :
    GenSm → WitUniq → WitComp → WitForget → WitOne := by
  intro hS hU hC hF p _ D G L R _ _ gb X N' N hA π Φ hW
  let M : Lv p := ⟨N.1 * N'.1, Nat.le_trans N.2.1 (Nat.le_mul_of_pos_right _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul_left N.2.2 N'.2.2⟩
  have hI : Integ L (1 : G.GAf) := fun v hv => by simpa using hv
  have hMN : AdmK L M.1 N.1 1 := fun u hu => by
    simpa using UpperTheory.Gal.Int.Geo.KN_anti (Dvd.intro _ rfl : N.1 ∣ M.1) hu
  obtain ⟨c, Φc, Wc, cF, cE, cS⟩ := hF p D G L R gb N' M (Dvd.intro_left _ rfl) (X N') (X M)
  obtain ⟨e, Φe, We, eF, eE, eS⟩ := hF p D G L R gb N M (Dvd.intro _ rfl) (X N) (X M)
  have W1 := (hC p D G L R gb M N' N (X M) (X N') (X N) 1 1).2 hI hA c Φc π Φ Wc hW
  rw [_root_.mul_one] at W1
  have hce : c ≫ π = e := (hU p D G L R gb M N (X M) (X N) 1 hI hMN _ _ _ _ W1 We).1
  obtain ⟨s1, s2, s3, -⟩ := hS p D R gb N' (X N')
  obtain ⟨t1, t2, t3, -⟩ := hS p D R gb N (X N)
  have hs : π ≫ (X N).s = (X N').s := hW.1
  have sep : IsSeparated (π ≫ (X N).s) := by rw [hs]; exact s2
  have lft : LocallyOfFiniteType (π ≫ (X N).s) := by rw [hs]; infer_instance
  have πS : IsSeparated π := IsSeparated.of_comp π (X N).s
  have πL : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π (X N).s
  have hE : Etale (c ≫ π) := by rw [hce]; exact eE
  have hFi : IsFinite (c ≫ π) := by rw [hce]; exact eF
  obtain ⟨r1, r2⟩ := GlobalTheory.etale_isFinite_of_comp_etale_surjective _ _ _ c π cE cS hE hFi πS πL
  have hSu : Surjective (c ≫ π) := by rw [hce]; exact eS
  exact ⟨r2, r1, Surjective.of_comp c π⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitTrans
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitTrans :
    KNBasic → PtEq → PtOrbit → WitComp → WitTrans := by
  intro hKN hEq hOrb hWC p _ D G L R _ _ gb X N' N π Φ hW k _ _ x y hxy
  obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, hθΦ⟩ := hOrb p D G L R gb N' N (X N') (X N) π Φ hW k x y hxy
  refine ⟨u, hu, fun π' Φ' hW' => ?_⟩
  have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
  have h1 : (1 : G.GAf) ∈ L.KN 1 := one_mem _
  have hid := (hWC p D G L R gb N' N' N' (X N') (X N') (X N') 1 1).1 1 (one_mem _)
  obtain ⟨hA, hB⟩ := hEq p D G L R gb N' N' N' (X N') (X N') (X N') u 1 u 1 π' Φ' (𝟙 _) (𝟙 _) hW' hid
    (UpperTheory.Gal.Int.Geo.integ_of_mem hu1) (UpperTheory.Gal.Int.Geo.integ_of_mem h1)
    ((hKN p D G L N').1 u hu1) ((hKN p D G L N').1 1 h1) (one_mem _) (by simp) k (x ≫ (X N').s) x y rfl hys
    ox oy mx my θ hθ
  refine ⟨by simpa using hA, fun a ha => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ mx.φ = a :=
    ⟨_, mx.cart.1.lift_fst a (𝟙 _) (by rw [ha, Category.id_comp])⟩
  simp only [Category.assoc]
  rw [reassoc_of% hB, hθΦ]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitUniq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitUniq :
    GenSm → ExtPts → TransSelf → PtEq → WitUniq := by
  intro hG hE hS hP p _ D G L R _ _ gb N' N X' X h ih ah π Φ π' Φ' w w'
  have hsm : Smooth X'.s := (hG p D R gb N' X').1
  haveI : IsSeparated X.s := (hG p D R gb N X).2.1
  haveI : AlgebraicGeometry.IsReduced X'.X := GlobalTheory.isReduced_of_smooth_of_isReduced X'.s
  have pt : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X'.X),
      ∃ ox : GObj gb N' (x ≫ X'.s), ∃ mx : GObjMap ox X'.univ x,
        x ≫ π = x ≫ π' ∧ mx.φ ≫ Φ = mx.φ ≫ Φ' := by
    intro Ω _ _ x
    obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl X'.univ
    have t := (hS p D G L R gb (Sp Ω) (x ≫ X'.s) N').1 ox 1 (L.KN N').one_mem
    have e := hP p D G L R gb N' N' N X' X' X h h 1 1 π Φ π' Φ' w w' ih ih ah ah
      (L.KN N).one_mem (by simp) Ω (x ≫ X'.s) x x rfl rfl ox ox mx mx (𝟙 _) t
    exact ⟨ox, mx, e.1, by simpa using e.2⟩
  have hπ : π = π' := hE X.s π π' (by rw [w.1, w'.1]) fun Ω _ _ x => by
    obtain ⟨_, _, e, _⟩ := pt Ω x
    exact e
  refine ⟨hπ, ?_⟩
  haveI := X'.univ.ab
  haveI := X.univ.ab
  haveI : Smooth X'.univ.A.hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced X'.univ.A.left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced X'.univ.A.hom
  haveI : IsProper X.univ.A.hom := IsAbelianScheme.proper
  refine hE X.univ.A.hom Φ Φ' (by rw [w.w, w'.w, hπ]) fun Ω _ _ z => ?_
  obtain ⟨ox, mx, -, e⟩ := pt Ω (z ≫ X'.univ.A.hom)
  obtain ⟨l, hl, -⟩ := mx.cart.1.exists_lift z (𝟙 _) (by simp)
  calc z ≫ Φ = l ≫ mx.φ ≫ Φ := by rw [← Category.assoc, hl]
    _ = l ≫ mx.φ ≫ Φ' := by rw [e]
    _ = z ≫ Φ' := by rw [← Category.assoc, hl]
end

