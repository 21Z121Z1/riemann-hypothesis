import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0145

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientMapComp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Int.Geo.QCompPf

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {b : Base D R} {gb : GBase D.toG R'} {N N₀ c : ℕ} {X X' X₁ X₂ : Scheme.{0}} {s : X ⟶ Sp R'}
  {s' : X' ⟶ Sp R'} {s₁ : X₁ ⟶ Sp R} {s₂ : X₂ ⟶ Sp R} {o : GObj gb N s} {o' : GObj gb N s'}
  {u₁ : Obj b N₀ s₁} {u₂ : Obj b N₀ s₂} {f : X ⟶ X₁} {g : X₁ ⟶ X₂} {e : X' ⟶ X}

private def after (n : QMap o u₁ f c) (m : ObjMap u₁ u₂ g) : QMap o u₂ (f ≫ g) c where
  φ := n.φ ≫ m.φ
  φ₂ := n.φ₂ ≫ m.φ₂
  cart := n.cart.comp m.cart
  sq := MapComp.isSquare_comp n.sq m.sq
  act x := by
    have h₁ := n.act x
    have h₂ := m.act x
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]
  pol := (n.pol).trans o.isLB (pull_isLB u₁.isLB _) (pull_isLB u₂.isLB _)
    (MapComp.lbIso_pull_comp m.pol n.φ₂ rfl)
  eta y := by
    have h₁ := n.eta y
    have h₂ := m.eta y
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]

private def before (m : GObjMap o' o e) (n : QMap o u₁ f c) : QMap o' u₁ (e ≫ f) c where
  φ := m.φ ≫ n.φ
  φ₂ := m.φ₂ ≫ n.φ₂
  cart := m.cart.comp n.cart
  sq := MapComp.isSquare_comp m.sq n.sq
  act x := by
    have h₁ := m.act x
    have h₂ := n.act x
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]
  pol := (m.pol).trans o'.isLB (pull_isLB o.isLB _) (pull_isLB u₁.isLB _)
    (MapComp.lbIso_pull_comp n.pol m.φ₂ rfl)
  eta y := by
    have h₁ := m.eta (c • y)
    have h₂ := n.eta y
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]

private theorem factor (n' : QMap o u₂ (f ≫ g) c) (m : ObjMap u₁ u₂ g) :
    ∃ n : QMap o u₁ f c, n'.φ = n.φ ≫ m.φ := by
  have hw : n'.φ ≫ u₂.A.hom = (o.A.hom ≫ f) ≫ g := by
    rw [n'.cart.1.w, Category.assoc]
  let ℓ : o.A.left ⟶ u₁.A.left := m.cart.1.lift n'.φ (o.A.hom ≫ f) hw
  have hℓφ : ℓ ≫ m.φ = n'.φ := m.cart.1.lift_fst _ _ _
  have hℓs : ℓ ≫ u₁.A.hom = o.A.hom ≫ f := m.cart.1.lift_snd _ _ _
  obtain ⟨ℓ₂, hsq⟩ := MapComp.exists_isSquare (G := u₁.A) (G' := o.A) hℓs
  have hsq₂ : ℓ₂ ≫ m.φ₂ = n'.φ₂ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp hsq m.sq)
    rw [hℓφ]
    exact n'.sq
  refine ⟨⟨ℓ, ℓ₂, ?_, hsq, ?_, ?_, ?_⟩, hℓφ.symm⟩
  · exact IsGrpPullback.cancel m.cart (IsGrpPullback.congr n'.cart rfl hℓφ.symm) hℓs
  · intro x
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hℓφ, m.act x, ← Category.assoc, hℓφ]
      exact n'.act x
    · rw [Category.assoc, Category.assoc, hℓs, Over.w, hℓs, ← Category.assoc, Over.w]
  · exact LBIso.trans o.isLB (pull_isLB u₂.isLB _) (pull_isLB u₁.isLB _) n'.pol
      (MapComp.lbIso_pull_comp m.pol ℓ₂ hsq₂.symm).symm
  · intro y
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hℓφ, n'.eta y, m.eta y, Category.assoc]
    · rw [Category.assoc, Category.assoc, hℓs, ← Category.assoc, Over.w]
      simp [Over.w]

private theorem bridge [IsIso f] (n : QMap o u₁ f c) (n' : QMap o u₂ (f ≫ g) c) :
    ∃ m : ObjMap u₁ u₂ g, n'.φ = n.φ ≫ m.φ := by
  haveI hiso : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  have hinvw : inv n.φ ≫ o.A.hom = u₁.A.hom ≫ inv f := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, n.cart.1.w, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hinv : IsGrpPullback u₁.A o.A (inv f) (inv n.φ) :=
    IsGrpPullback.cancel n.cart
      (IsGrpPullback.congr (GlobalTheory.EndLoc.isGrpPullback_id u₁.A) (by simp) (by simp)) hinvw
  have hcart : IsGrpPullback u₁.A u₂.A g (inv n.φ ≫ n'.φ) :=
    IsGrpPullback.congr (IsGrpPullback.comp hinv n'.cart) (by simp) rfl
  obtain ⟨ψ₂, hψ⟩ := MapComp.exists_isSquare (G := o.A) (G' := u₁.A) hinvw
  have hid : Geo.Tor.IsSquare (𝟙 u₁.A.left) (𝟙 (u₁.A ⊗ u₁.A).left) := by
    constructor <;> simp
  have hψn : ψ₂ ≫ n.φ₂ = 𝟙 _ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp hψ n.sq)
    rw [IsIso.inv_hom_id]
    exact hid
  refine ⟨⟨inv n.φ ≫ n'.φ, ψ₂ ≫ n'.φ₂, hcart, MapComp.isSquare_comp hψ n'.sq, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    have hx : Over.Hom.left (u₁.act.act x) ≫ inv n.φ = inv n.φ ≫ Over.Hom.left (o.act.act x) := by
      rw [IsIso.comp_inv_eq, Category.assoc, n.act x, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, hx, Category.assoc, n'.act x, Category.assoc]
  · exact LBIso.trans u₁.isLB (pull_isLB u₁.isLB _) (pull_isLB u₂.isLB _)
      (GlobalTheory.SiegLower.lbIso_pull_id u₁.isLB)
      (LBIso.trans (pull_isLB u₁.isLB _) (pull_isLB o.isLB _) (pull_isLB u₂.isLB _)
        (MapComp.lbIso_pull_comp n.pol ψ₂ hψn.symm).symm
        (MapComp.lbIso_pull_comp n'.pol ψ₂ rfl))
  · intro y
    have hy : Over.Hom.left (u₁.eta y) = inv f ≫ Over.Hom.left (o.eta (c • y)) ≫ n.φ := by
      rw [n.eta y, IsIso.inv_hom_id_assoc]
    rw [hy]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, n'.eta y, IsIso.inv_hom_id_assoc]
  · simp

end UpperTheory.Gal.Int.Geo.QCompPf

open UpperTheory.Gal.Int.Geo.QCompPf in
theorem UpperTheory.quotient_map_comp : QComp := by
  intro q _ D R R' _ _ _ b gb N N₀ c X X₁ X₂ s s₁ s₂ o u₁ u₂ f g
  refine ⟨fun n m => ⟨after n m, rfl⟩, fun n' m => factor n' m, fun hf n n' => bridge n n', ?_⟩
  intro X' s' o' e m n
  exact ⟨before m n, rfl⟩
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
section
open CategoryTheory UpperTheory.Gal.Int.Geo

theorem UpperTheory.quotient_unique_of_comp :
    QComp → QUniq := by
  intro hQ q _ D R R' _ _ _ b gb N N₀ c h3 hc X X₁ s s₁ o u f n n'
  obtain ⟨u', ⟨m⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback q D R b N₀ X₁ X s₁ (f ≫ s₁) f rfl u

  have down : ∀ k : QMap o u f c, ∃ k₁ : QMap o u' (𝟙 X) c, k.φ = k₁.φ ≫ m.φ := by
    intro k
    obtain ⟨k₀, hk⟩ : ∃ k₀ : QMap o u (𝟙 X ≫ f) c, k₀.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨k₁, h₁⟩ := (hQ q D R R' b gb N N₀ c X X X₁ s (f ≫ s₁) s₁ o u' u (𝟙 X) f).2.1 k₀ m
    exact ⟨k₁, hk ▸ h₁⟩
  obtain ⟨n₁, h₁⟩ := down n
  obtain ⟨n₂, h₂⟩ := down n'

  have self : ∀ k : QMap o u' (𝟙 X) c, ∃ a : GlobalTheory.UPel.HT.ObjMap u' u' (𝟙 X), k.φ = n₁.φ ≫ a.φ := by
    intro k
    obtain ⟨k₀, hk⟩ : ∃ k₀ : QMap o u' (𝟙 X ≫ 𝟙 X) c, k₀.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨a₀, ha₀⟩ : ∃ a : GlobalTheory.UPel.HT.ObjMap u' u' (𝟙 X), k₀.φ = n₁.φ ≫ a.φ :=
      (hQ q D R R' b gb N N₀ c X X X s (f ≫ s₁) (f ≫ s₁) o u' u' (𝟙 X) (𝟙 X)).2.2.1
        inferInstance n₁ k₀
    exact ⟨a₀, hk ▸ ha₀⟩
  obtain ⟨a, ha⟩ := self n₁
  obtain ⟨a', ha'⟩ := self n₂
  have hr : a.φ = a'.φ := GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique q D R b N₀ h3 hc X X (f ≫ s₁) (f ≫ s₁) u' u' (𝟙 X) a a'
  rw [h₁, h₂, ha', ← hr, ← ha]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RationalSplittingExists
section
open UpperTheory.Gal.Int.Geo

private theorem matrix_unique_algEquiv (R A m : Type) [CommSemiring R] [Semiring A] [Algebra R A]
    [fm : Fintype m] [dm : DecidableEq m] [Unique m] : Nonempty (Matrix m m A ≃ₐ[R] A) := by
  refine ⟨{ toFun := fun M => M default default
            invFun := fun a => Matrix.of fun _ _ => a
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_
            map_add' := ?_
            commutes' := ?_ }⟩
  · intro M
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  · intro a
    simp
  · intro M N
    simp [Matrix.mul_apply]
  · intro M N
    simp
  · intro r
    simp [Matrix.algebraMap_matrix_apply]

open scoped TensorProduct in
theorem UpperTheory.rational_splitting_exists :
    SplitQ := by
  intro p _ D hm q _
  haveI : Unique (Fin D.m) :=
    { default := ⟨0, by omega⟩
      uniq := fun i => Fin.ext (by have := i.2; simp; omega) }
  let e0 : D.O ≃ₐ[NumberField.RingOfIntegers D.F] NumberField.RingOfIntegers D.F :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _)
      ⟨D.algebraMap_injective hm, GlobalTheory.T.integers_surjective_of_rank_one p D hm⟩).symm
  exact ⟨(Algebra.TensorProduct.congr e0 AlgEquiv.refl).trans
    (matrix_unique_algEquiv _ _ _).some.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SiteExistsOfSplittingAndPowerProjector
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.site_exists_of_splitting_and_power_projector :
    MIn → SplitQ → BaseEx → PowProj → SiteEx := by
  intro hM hS hB hP
  intro p _ D G hSc E _ _ e gb hstd w q _ r 𝔴 𝔫 hpl hat hlev
  have sp := hS p D hSc.m1 q
  obtain ⟨N₀, 𝔞, h3, hcq, hcp, hsup, hupow, hlv⟩ := hlev
  obtain ⟨f, b, hmat, hstdb, hqmem, hnorm⟩ :=
    hB q (datAt hat sp) hSc.a1 hSc.m1 E e gb hstd w 𝔴 r hpl hat.le N₀ h3 hcq
  obtain ⟨M⟩ := hM.ex q (datAt hat sp) (Ow w) b N₀ h3 hcq
  have hEt : UpperTheory.Gal.FiniteEtaleModels.IsEtIdeal b 𝔞 :=
    (hM.placeOf q (datAt hat sp) (Ow w) b r 𝔴 hat.max hstdb.pmem hSc.a1 hstdb.ule hstdb.tw 𝔞 hsup).2 hupow
  obtain ⟨Y, π, ρ, hov, ⟨hmπ⟩, hgal⟩ := hM.finModel q (datAt hat sp) (Ow w) b N₀ h3 hcq 𝔞 1 hEt M
  have hfin : IsFinite π := hgal.fin
  have het : Etale π := hgal.etale
  have hMproj : IsProjOver M.s := hM.proj q (datAt hat sp) (Ow w) b N₀ h3 hcq hSc.cpt M
  have hYproj : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.T.isProjOver_comp_finite (Ow w) M.X Y.X π M.s hfin hMproj
  have hYsm : SmoothOfRelativeDimension (0 + (datAt hat sp).a * ((datAt hat sp).n - 1)) Y.s := by
    rw [← hov]
    haveI : SmoothOfRelativeDimension 0 π := by
      rw [← AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero]
      exact het
    haveI := M.smooth
    infer_instance
  have hPw := fun k => hP q (datAt hat sp) (Ow w) b N₀ h3 hcq Y.X Y.s Y.univ k
  exact ⟨⟨hat, sp, f, b, hmat, N₀, 𝔞, hstdb, hqmem, hnorm, hcp, hsup, hupow, hlv, M, Y, π, hov, hmπ,
    hfin, het, fun k => (hPw k).1 hYproj, fun k => (hPw k).2 _ hYsm⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerCoveringCongruenceOfHeckeLies
section
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.tower_covering_congruence_of_hecke_lies :
    MIn → SiteEx → NumEx → ClsEx → KSCover → TjLies → KSCong := by
  intro hM hS hN hC hV hL p _ D G L hsc E _ _ e gb hstd k T N J A _ g θ w 𝔴 hpl ϑ hG
  obtain ⟨q, r, 𝔫, K₀, hat, hok, hlev, hKN, hNn, hdeck, hall⟩ := hG
  haveI : Fact q.Prime := ⟨hat.prime⟩
  haveI : 𝔴.IsMaximal := hat.max
  obtain ⟨S⟩ := hS p D G hsc E e gb hstd w q r 𝔴 𝔫 hpl hat hok
  have hNpos : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  obtain ⟨c, a, hnum⟩ := (hN p D E gb w q r 𝔴 𝔫 S N.1 hNpos).1 hNn
  obtain ⟨⟨C⟩, -⟩ := hC q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat N.1 S.N₀ c a S.𝔞
    hnum.1 hNpos S.std.three S.std.cop hnum.2 S.Y (T.M N).X (T.M N).s (T.M N).univ
  obtain ⟨Cv⟩ := hV p D G L E gb w q r 𝔴 𝔫 S k T K₀ hlev N c a hnum C hKN J A g θ hdeck
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  haveI := S.et
  obtain ⟨Tc, Lc, d, h, hov, hpt⟩ := hM.cong q (datAt S.atq S.sp) (Ow w) S.f S.b S.N₀ r 𝔴 S.std S.M ϖ hϖ S.𝔞 1
    S.sup S.upow S.Y S.π S.ov inferInstance S.mπ k
  choose γ hγK hγT hγd hγr hγθ using hall
  refine ⟨Cv.toCover, q, S.f, hat.prime, S.qmem, S.norm, ϖ, fun j => (h j).corr,
    fun j => γ j (Nat.lt_succ_iff.1 j.2), fun j => (L.KN (g (γ j (Nat.lt_succ_iff.1 j.2))).M.1).relIndex
      (K₀ ⊓ K₀.comap (MulAut.conj (g (γ j (Nat.lt_succ_iff.1 j.2))).h).toMonoidHom), hϖ, hpt, fun j => ⟨hov j, ?_, ?_⟩⟩
  · obtain ⟨h0, κ, e1, e2, e3⟩ := hL p D G L E gb w q r 𝔴 𝔫 S k T K₀ hlev N c a hnum C hKN J g _ j
      (Nat.lt_succ_iff.1 j.2) (hγK _ _) (hγT _ _) (hγd _ _) (hγr _ _) (Tc j) (Lc j)
    exact ⟨h0, κ, e1, e2, e3⟩
  · exact hγθ _ _
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerFiniteEtaleOfTrivialPowerCartesian
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.Int.Geo

set_option maxHeartbeats 800000 in
theorem UpperTheory.tower_finiteEtale_of_trivial_powerCartesian :
    PiZero → PowCart → PiFet := by
  intro h0 hpc p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T N c a hN C
  obtain ⟨ρ, e0, hop, hcl, htr⟩ := h0 p D G L E gb w q r 𝔴 𝔫 S k T N c a hN C
  have hx : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have hN' : (N : ℕ) = S.N₀ * c := by
    unfold Site.Num at hN
    exact hN.1
  have hsub : ∀ (n m : ℕ) (g : G.GAf), L.CongOne (n * m) g → L.CongOne n g := by
    intro n m g hg
    unfold GlobalTheory.LKGeo.Link.CongOne at hg ⊢
    intro v hv
    obtain ⟨u, hu, huv⟩ := hg v hv
    exact ⟨m • u, AddSubgroup.nsmul_mem _ hu m, by rw [huv, mul_smul]⟩
  obtain ⟨hy, htr'⟩ : ∃ hy, T.X.tr (T.lev N) _ 1 hx hy ≫ ρ = _ := ⟨_, htr hx (by
    intro u hu
    rw [one_mul, inv_one, mul_one]
    rw [T.3] at hu ⊢
    rw [hN'] at hu
    show u ∈ L.KN S.N₀
    unfold GlobalTheory.LKGeo.Link.KN at hu ⊢
    exact ⟨hsub _ _ _ hu.1, hsub _ _ _ hu.2⟩)⟩
  have hG := S.mπ.3
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback at hG
  have hpb := hG.1
  obtain ⟨hP1, hP2, -⟩ := hpc S.Y.X S.M.X S.M.X S.Y.univ.A S.M.univ.A S.M.univ.A S.π (𝟙 _) S.mπ.φ (𝟙 _)
    hpb.w (by simp) k
  have hPB := hP1 hpb
  have hfinP : IsFinite (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hPB.flip S.20
  have hetP : Etale (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) :=
    MorphismProperty.of_isPullback (P := @Etale) hPB.flip S.21
  have hcomm : (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s =
      GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s := by
    rw [← Category.assoc, hP2, Category.assoc, S.18]
  have eY : S.pi T C ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s = T.X.q (T.lev N) ≫ gen (Ow w) E := by
    rw [hcomm, ← Category.assoc, ← htr', Category.assoc, e0, ← Category.assoc, T.X.10]
  refine ⟨eY, ?_⟩
  have h1 : ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) ≫ 𝟙 _ =
      GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s := by
    rw [Category.comp_id, hcomm]
  have h2 : gen (Ow w) E ≫ 𝟙 _ = 𝟙 _ ≫ gen (Ow w) E := by
    rw [Category.comp_id, Category.id_comp]
  let hm := pullback.map ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) (gen (Ow w) E)
    ((GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s) (gen (Ow w) E)
    (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) (𝟙 _) (𝟙 _) h1 h2
  have h3 : gen (Ow w) E = 𝟙 _ ≫ gen (Ow w) E := (Category.id_comp _).symm
  have hmF : IsFinite hm := MorphismProperty.pullback_map (P := @IsFinite) hfinP inferInstance hcomm h3
  haveI := hetP
  have hmU : FormallyUnramified hm :=
    MorphismProperty.pullback_map (P := @FormallyUnramified) inferInstance inferInstance hcomm h3
  have hkey : pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm =
      T.X.tr _ _ 1 hx hy ≫ pullback.lift ρ _ e0 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, htr']
      simp only [hm, pullback.lift_fst_assoc, pullback.map, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, T.X.10]
      simp only [hm, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  haveI := hop
  haveI := hcl
  haveI := T.X.13 _ _ hx hy
  haveI := T.X.14 _ _ hx hy
  have hcomp : IsFinite (pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm) ∧
      Etale (pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm) := by
    rw [hkey]
    exact ⟨inferInstance, inferInstance⟩
  haveI := hcomp.1
  haveI := hcomp.2
  exact ⟨IsFinite.of_comp _ hm, Etale.of_comp _ hm⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerInvariantOfBaseInvariantPowerCartesian
section
open UpperTheory.Gal.Int.Geo
open CategoryTheory AlgebraicGeometry

private theorem powMap_congr {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f f' : S' ⟶ S} {φ φ' : A'.left ⟶ A.left}
    (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f) (h' : φ' ≫ A.hom = A'.hom ≫ f') (k : ℕ) :
    GlobalTheory.KS.powMap f φ h k = GlobalTheory.KS.powMap f' φ' h' k := by
  subst hf hφ
  rfl

theorem UpperTheory.tower_invariant_of_base_invariant_powerCartesian :
    BaseInv → PowCart → PiInv := by
  intro hB hP p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu x y
  obtain ⟨π, o, ψ, φ, hw, ov, tr, e⟩ := T.tr_eq N' N u x y
  obtain ⟨h1, h2⟩ := hB p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu
    ⟨π, o, ψ, φ, ov, tr⟩
  have h1' : π ≫ C.j = C'.j := h1
  have h2' : (ψ.left ≫ φ.φ) ≫ C.m.φ = C'.m.φ := by
    rw [Category.assoc]; exact h2
  have hv := C.m.cart.1.w
  have hw' : ((ψ.left ≫ φ.φ) ≫ C.m.φ) ≫ S.Y.univ.A.hom = (T.M N').univ.A.hom ≫ π ≫ C.j := by
    rw [Category.assoc, hv, ← Category.assoc, hw, Category.assoc]
  have hc := (hP _ _ _ (T.M N').univ.A (T.M N).univ.A S.Y.univ.A π C.j (ψ.left ≫ φ.φ) C.m.φ hw hv k).2.2 hw'
  simp only [Site.pi, Cls.pw]
  rw [← Category.assoc, e, Category.assoc, hc]
  exact congrArg _ (powMap_congr h1' h2' _ _ k)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerPointCountStatement
section
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.tower_point_count_statement :
    Count := by
  intro Γ _ K₀ H K hKH hHK₀ hK F κ hF hκ ζ
  classical
  have hmul : K.relIndex H * H.relIndex K₀ = K.relIndex K₀ :=
    Subgroup.relIndex_mul_relIndex K H K₀ hKH hHK₀
  have hKH0 : K.relIndex H ≠ 0 := fun h0 => hK (by rw [← hmul, h0, zero_mul])
  have hH0 : H.relIndex K₀ ≠ 0 := fun h0 => hK (by rw [← hmul, h0, mul_zero])
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact hH0)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (↥K₀ ⧸ K.subgroupOf K₀) := Nat.finite_of_card_ne_zero hK
  haveI : Finite (↥H ⧸ K.subgroupOf H) := Nat.finite_of_card_ne_zero hKH0
  have bound : ∀ ξ : F, Nat.card {x // κ x = ξ} ≤ K.relIndex H := by
    intro ξ
    by_cases hne : Nonempty {x // κ x = ξ}
    · obtain ⟨⟨q0, hq0⟩⟩ := hne
      have memH : ∀ q : {x // κ x = ξ},
          ((q0.out : ↥K₀) : Γ)⁻¹ * ((q.1.out : ↥K₀) : Γ) ∈ H := by
        intro q
        apply hκ
        rw [QuotientGroup.out_eq', QuotientGroup.out_eq', hq0, q.2]
      let f : {x // κ x = ξ} → ↥H ⧸ K.subgroupOf H := fun q => ((⟨_, memH q⟩ : ↥H) : ↥H ⧸ K.subgroupOf H)
      have hinj : Function.Injective f := by
        intro q1 q2 h12
        have h' := QuotientGroup.eq.mp h12
        rw [Subgroup.mem_subgroupOf] at h'
        apply Subtype.ext
        rw [← QuotientGroup.out_eq' q1.1, ← QuotientGroup.out_eq' q2.1]
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using h'
      calc Nat.card {x // κ x = ξ} ≤ Nat.card (↥H ⧸ K.subgroupOf H) :=
            Nat.card_le_card_of_injective f hinj
        _ = K.relIndex H := rfl
    · haveI := not_nonempty_iff.mp hne
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have hsum : ∑ ξ : F, Nat.card {x // κ x = ξ} = ∑ ξ : F, K.relIndex H := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv κ), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hF, mul_comm, hmul]
    rfl
  exact (Finset.sum_eq_sum_iff_of_le (fun ξ _ => bound ξ)).mp hsum ζ (Finset.mem_univ _)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaPointwise
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.trace_eta_pointwise : TrEtaPt := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x
  obtain ⟨-, -, -, -, hgeo⟩ := hT
  have hz : z ≫ s = spMap (Spec.preimage (z ≫ s)).hom := by
    simp [spMap, Spec.map_preimage]
  obtain ⟨I', I'', h1, h2, h3⟩ := hgeo Ω z _ hz
  have hpos : ∀ M : Lv p, 0 < (M : ℕ) := fun M => by
    have := M.2.1
    omega
  have hzero : ∀ n : ℕ, I''.ev n 0 = 1 := fun n => by
    have h := I''.add n 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hin0 : inAf D 0 = 0 := by
    simp [inAf]
  have e1 := congrArg (· ≫ ψ) (h1 x)
  simp only [Category.assoc] at e1
  refine ⟨?_, ?_⟩
  · refine Iff.trans ?_ ((h3 _ (hpos N') N'.2.2 x 0).trans ?_)
    · rw [e1]
      first
        | simp only [hzero]
        | erw [hzero]
    · simp only [hin0, zero_add]
  · rintro rfl y hxy
    refine (h3 _ (hpos N') N'.2.2 x y).mp ?_
    rw [← e1, hxy]
    exact h2 y
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceUnitOfPullbackMultiplier
section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open UpperTheory.Gal.Int.Geo

private theorem unit_aux {A : Type} [CommRing A] {m c t t' s : A} (hm : m = c * t) (ht : t * t' = 1)
    (hs : m * s = 1) : c = 1 * (m * t') ∧ (m * t') * (t * s) = 1 := by
  constructor
  · rw [_root_.one_mul, hm, _root_.mul_assoc, ht, _root_.mul_one]
  · calc (m * t') * (t * s) = (m * s) * (t * t') := by ring
      _ = 1 := by rw [hs, ht, _root_.one_mul]

theorem UpperTheory.trace_unit_of_pullback_multiplier :
    TrBack → MultUnit → TrUnit := by
  intro hB hM p _ D G L R _ _ gb h X s N' N o' o ψ hT hh
  obtain ⟨ψ', -, e₁, e₂⟩ := hB p D G L R gb h X s N' N o' o ψ hT 1 (Nat.coprime_one_left p)
    (fun v hv => ⟨L.actG h⁻¹ v, integ_of_mem (inv_mem hh) v hv, by
      rw [one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩)
  have hiso : CategoryTheory.IsIso ψ := ⟨ψ', e₁.trans (pow_one _), e₂.trans (pow_one _)⟩
  refine ⟨hiso, ?_⟩
  obtain ⟨-, -, -, ⟨c, hc, hP, t, t', ht, ht', htt, hm⟩, -⟩ := hT
  obtain ⟨hu, hfix⟩ := hM p D G L
  obtain ⟨s', hi, hs, hs1⟩ := hu h hh
  obtain ⟨a₁, a₂⟩ := unit_aux hm htt hs1
  have hint : ∀ {a b : GlobalTheory.LKTrip.AfP p}, GlobalTheory.LKGeo.IsIntAf a → GlobalTheory.LKGeo.IsIntAf b → GlobalTheory.LKGeo.IsIntAf (a * b) := fun ha hb v => by
    rw [map_mul]; exact mul_mem (ha v) (hb v)
  have hc1 : c = 1 := hfix c 1 _ _ hc (Nat.coprime_one_left p) (hint hi ht') (hint ht hs) a₂
    (by rw [Nat.cast_one]; exact a₁)
  subst hc1
  exact hP
end

