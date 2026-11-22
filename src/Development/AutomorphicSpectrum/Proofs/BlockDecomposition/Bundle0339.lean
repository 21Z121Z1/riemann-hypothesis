import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0326
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0328
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InductionReindexEquiv
section
set_option maxSynthPendingDepth 1

noncomputable section

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.CompanionTheory.SmGLBridge

namespace GlobalTheory.CompanionTheory.ParIndReindex

section Generic

variable {G G' V V' W : Type} [Group G] [Group G']
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]

theorem twKer_map (r : G ≃* G') (L : V ≃ₗ[ℂ] V') {π : Representation ℂ G V}
    {π' : Representation ℂ G' V'} (hL : ∀ g v, L (π g v) = π' (r g) (L v))
    {N : Subgroup G} {N' : Subgroup G'} (hN : ∀ g, g ∈ N ↔ r g ∈ N') :
    (twKer π N 1).map (L : V →ₗ[ℂ] V') = twKer π' N' 1 := by
  delta GlobalTheory.PRep.twKer
  rw [Submodule.map_span]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨n, v, rfl⟩, rfl⟩
    exact ⟨⟨r n, (hN n).1 n.2⟩, L v, by simp [hL]⟩
  · rintro ⟨n', v', rfl⟩
    refine ⟨_, ⟨⟨r.symm n', (hN _).2 (by simpa using n'.2)⟩, L.symm v', rfl⟩, ?_⟩
    simp [hL]

def jacquetEquiv (r : G ≃* G') (L : V ≃ₗ[ℂ] V') {π : Representation ℂ G V}
    {π' : Representation ℂ G' V'} (hL : ∀ g v, L (π g v) = π' (r g) (L v))
    {N : Subgroup G} {N' : Subgroup G'} (hN : ∀ g, g ∈ N ↔ r g ∈ N') :
    Jacquet π N ≃ₗ[ℂ] Jacquet π' N' :=
  Submodule.Quotient.equiv _ _ L (twKer_map r L hL hN)

def pullFun (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f : indSpace H' σ') : indSpace H σ :=
  ⟨fun x => f.1 (r x), fun h g => by
    show f.1 (r (h * g)) = σ h (f.1 (r g))
    rw [map_mul, ← hσ h]
    exact f.2 ⟨r h, hH h⟩ (r g)⟩

theorem ind_pullFun (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f : indSpace H' σ') (g : G) :
    ind H σ g (pullFun r hH hσ f) = pullFun r hH hσ (ind H' σ' (r g) f) := by
  apply Subtype.ext
  funext x
  show f.1 (r (x * g)) = f.1 (r x * r g)
  rw [map_mul]

theorem pullFun_eq_iff (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f f' : indSpace H' σ') :
    pullFun r hH hσ f = pullFun r hH hσ f' ↔ f = f' := by
  constructor
  · intro h
    apply Subtype.ext
    funext y
    have h1 : f.1 (r (r.symm y)) = f'.1 (r (r.symm y)) :=
      congrArg (fun p : indSpace H σ => p.1 (r.symm y)) h
    simpa using h1
  · rintro rfl
    rfl

variable [TopologicalSpace G] [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']

def pull (r : G ≃* G') (hr : Continuous r) {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) :
    smoothPart (ind H' σ') →ₗ[ℂ] smoothPart (ind H σ) where
  toFun f := ⟨pullFun r hH hσ f.1, by
    have hset : {g : G | ind H σ g (pullFun r hH hσ f.1) = pullFun r hH hσ f.1} =
        r ⁻¹' {g' : G' | ind H' σ' g' f.1 = f.1} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, ind_pullFun, pullFun_eq_iff]
    show IsOpen {g : G | ind H σ g (pullFun r hH hσ f.1) = pullFun r hH hσ f.1}
    rw [hset]
    exact IsOpen.preimage hr f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def indEquiv (r : G ≃* G') (hr : Continuous r) (hs : Continuous r.symm) {H : Subgroup G}
    {H' : Subgroup G'} (hH : ∀ g, g ∈ H ↔ r g ∈ H') {σ : Representation ℂ H W}
    {σ' : Representation ℂ H' W} (hσ : ∀ h : H, σ' ⟨r h, (hH h).1 h.2⟩ = σ h) :
    smoothPart (ind H σ) ≃ₗ[ℂ] smoothPart (ind H' σ') :=
  LinearEquiv.ofLinear
    (pull r.symm hs (fun h' => (hH _).2 (by simp)) (fun h' => by
      rw [← hσ ⟨r.symm h', (hH _).2 (by simp)⟩]
      congr 1
      exact Subtype.ext (by simp)))
    (pull r hr (fun h => (hH h).1 h.2) hσ)
    (LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (r (r.symm x)) = _
      simp)))
    (LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (r.symm (r x)) = _
      simp)))

end Generic

section Reindex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {N : ℕ}

theorem glReindex_apply (ι : n ≃ Fin N) (g : GL n k) (i j : n) :
    ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (ι i) (ι j) =
      (g : Matrix n n k) i j := by
  show (Matrix.reindexAlgEquiv k k ι (g : Matrix n n k)) (ι i) (ι j) = (g : Matrix n n k) i j
  simp [Matrix.coe_reindexAlgEquiv]

theorem mem_parab_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k) :
    g ∈ parab k e ↔ glReindex ι g ∈ parab k (e.trans ι) := by
  show (g : Matrix n n k).BlockTriangular (blk e) ↔
    ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular (blk (e.trans ι))
  constructor
  · intro h i j hij
    have h2 := @h (ι.symm i) (ι.symm j) (by simpa [blk] using hij)
    have e1 := glReindex_apply ι g (ι.symm i) (ι.symm j)
    simp only [Equiv.apply_symm_apply] at e1
    rw [e1]
    exact h2
  · intro h i j hij
    have h2 := @h (ι i) (ι j) (by simpa [blk] using hij)
    rw [glReindex_apply] at h2
    exact h2

private theorem leviProj_glReindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k)
    (h : g ∈ parab k e) (h' : glReindex ι g ∈ parab k (e.trans ι)) :
    leviProj k (e.trans ι) ⟨glReindex ι g, h'⟩ = leviProj k e ⟨g, h⟩ := by
  funext a
  apply Units.ext
  ext i j
  show ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (ι (e ⟨a, i⟩)) (ι (e ⟨a, j⟩)) =
    (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩)
  exact glReindex_apply ι g _ _

theorem mem_unipRad_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k) :
    g ∈ unipRad k e ↔ glReindex ι g ∈ unipRad k (e.trans ι) := by
  show g ∈ Subgroup.map (parab k e).subtype (leviProj k e).ker ↔
    glReindex ι g ∈ Subgroup.map (parab k (e.trans ι)).subtype (leviProj k (e.trans ι)).ker
  simp only [Subgroup.mem_map, MonoidHom.mem_ker]
  constructor
  · rintro ⟨⟨p, hp'⟩, hp, rfl⟩
    refine ⟨⟨glReindex ι p, (mem_parab_reindex e ι p).1 hp'⟩, ?_, rfl⟩
    rw [leviProj_glReindex e ι p hp']
    exact hp
  · rintro ⟨⟨p, hp'⟩, hp, hpg⟩
    simp only [Subgroup.coe_subtype] at hpg
    subst hpg
    have hg : g ∈ parab k e := (mem_parab_reindex e ι g).2 hp'
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [leviProj_glReindex e ι g hg hp'] at hp
    exact hp

theorem leviProj_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (p : parab k e) :
    leviProj k (e.trans ι) ⟨glReindex ι p, (mem_parab_reindex (k := k) e ι p.1).1 p.2⟩ = leviProj k e p := by
  exact leviProj_glReindex e ι p.1 p.2 _

theorem leviEmb_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : Levi k m) :
    glReindex ι (leviEmb k e g) = leviEmb k (e.trans ι) g := by
  apply Units.ext
  ext i j
  have h1 := glReindex_apply (k := k) ι (leviEmb k e g) (ι.symm i) (ι.symm j)
  simp only [Equiv.apply_symm_apply] at h1
  rw [h1]
  rfl

theorem continuous_glReindex_symm (ι : n ≃ Fin N) :
    Continuous (glReindex (k := k) ι).symm := by
  have h1 : ⇑(glReindex (k := k) ι).symm = ⇑(glReindex (k := k) ι.symm) :=
    funext (glReindex_symm ι)
  rw [h1]
  exact continuous_glReindex ι.symm

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def parIndEquiv (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (ρ : Representation ℂ (Levi k m) W) :
    IndSp e ρ ≃ₗ[ℂ] IndSp (e.trans ι) ρ :=
  indEquiv (glReindex ι) (continuous_glReindex ι) (continuous_glReindex_symm ι)
    (mem_parab_reindex e ι) (fun h => by
      show (twist ρ (deltaHalf k m)) (leviProj k (e.trans ι) _) = (twist ρ (deltaHalf k m)) (leviProj k e h)
      rw [leviProj_reindex])

theorem parIndEquiv_apply (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (ρ : Representation ℂ (Levi k m) W)
    (g : GL n k) (f : IndSp e ρ) :
    parIndEquiv e ι ρ (parInd e ρ g f) = parInd (e.trans ι) ρ (glReindex ι g) (parIndEquiv e ι ρ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  show f.1.1 ((glReindex ι).symm y * g) = f.1.1 ((glReindex ι).symm (y * glReindex ι g))
  rw [map_mul, MulEquiv.symm_apply_apply]

end Reindex

theorem jac_parInd_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' n : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n) {N : ℕ} (ι : n ≃ Fin N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((jac e' (parInd e ρ)).Equiv (jac (e'.trans ι) (parInd (e.trans ι) ρ))) := by
  intro k _ _ _ _ α β' n _ _ _ _ _ _ m _ _ m' _ _ e e' N ι W _ _ ρ
  refine ⟨Representation.Equiv.mk
    (jacquetEquiv (glReindex (k := k) ι) (parIndEquiv e ι ρ) (parIndEquiv_apply e ι ρ)
      (mem_unipRad_reindex e' ι)) (fun l => ?_)⟩
  apply LinearMap.ext
  intro y
  obtain ⟨v, rfl⟩ := Quot.exists_rep y
  have h1 := parIndEquiv_apply e ι ρ (leviEmb k e' l) v
  rw [leviEmb_reindex] at h1
  have h2 : parIndEquiv e ι ρ ((((deltaHalf k m')⁻¹ l : ℂˣ) : ℂ) • parInd e ρ (leviEmb k e' l) v) =
      (((deltaHalf k m')⁻¹ l : ℂˣ) : ℂ) •
        parInd (e.trans ι) ρ (leviEmb k (e'.trans ι) l) (parIndEquiv e ι ρ v) := by
    rw [LinearEquiv.map_smul, h1]
  exact congrArg (Quot.mk _) h2

end GlobalTheory.CompanionTheory.ParIndReindex
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsQuasicoherentOfSecsImage
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.PSupp

lemma secs_mk {X : Scheme.{0}} {E F : X.Modules} (i : F ⟶ E) [Mono i] (V : X.Opens) :
    secs (Subobject.mk i) V = Set.range (i.app V) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso i).hom.app V x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso i).inv.app V x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_arrow]

lemma restrict_map_app {X : Scheme.{0}} (O : X.Opens) {Q P : X.Modules} (a : Q ⟶ P)
    (W : (O : Scheme.{0}).Opens) (y : Γ(Q.restrict O.ι, W)) :
    ((Scheme.Modules.restrictFunctor O.ι).map a).app W y =
      (P.restrictAppIso O.ι W).inv (a.app (O.ι ''ᵁ W) ((Q.restrictAppIso O.ι W).hom y)) :=
  rfl

theorem isQuasicoherent_of_secs_image {X : Scheme.{0}} (O : X.Opens) {P : X.Modules}
    {E : (O : Scheme.{0}).Modules} (hP : P.IsQuasicoherent) (hE : E.IsQuasicoherent)
    (f : P.restrict O.ι ⟶ E) (Bb : Subobject P) (hBb : (Bb : X.Modules).IsQuasicoherent)
    (B : Subobject E)
    (hB : ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W =
      (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) :
    (B : (O : Scheme.{0}).Modules).IsQuasicoherent := by
  let g : (Bb : X.Modules).restrict O.ι ⟶ E := (Scheme.Modules.restrictFunctor O.ι).map Bb.arrow ≫ f
  have hBr : ((Bb : X.Modules).restrict O.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor O.ι _
  have hs : ∀ U : (O : Scheme.{0}).affineOpens,
      secs B (U : (O : Scheme.{0}).Opens) =
        secs (Subobject.mk (kernel.ι (cokernel.π g))) (U : (O : Scheme.{0}).Opens) := by
    intro U
    rw [secs_mk, range_kernel_ι_cokernel_π_app g U.2, hB _ U.2]
    ext m
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨((Bb : X.Modules).restrictAppIso O.ι (U : (O : Scheme.{0}).Opens)).inv y, ?_⟩
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, restrict_map_app, Iso.inv_hom_id_apply]
    · rintro ⟨y, rfl⟩
      refine ⟨_, ⟨((Bb : X.Modules).restrictAppIso O.ι (U : (O : Scheme.{0}).Opens)).hom y, rfl⟩, ?_⟩
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, restrict_map_app]
  have hEq : B = Subobject.mk (kernel.ι (cokernel.π g)) :=
    le_antisymm ((GlobalTheory.T.subobject_le_iff_affine_sections _ _).2 fun U => (hs U).subset)
      ((GlobalTheory.T.subobject_le_iff_affine_sections _ _).2 fun U => (hs U).symm.subset)
  have hK : (kernel (cokernel.π g)).IsQuasicoherent := inferInstance
  rw [hEq]
  exact GlobalTheory.QCoh.isQuasicoherent_of_iso (Subobject.underlyingIso (kernel.ι (cokernel.π g))).symm

end GlobalTheory.CompanionTheory.GE.PSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquiv
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.JacquetEquiv

theorem nonempty_jacquetRep_equiv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (γ : Fin n → ℕ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin n) F) V) (π' : Representation ℂ (GL (Fin n) F) V'), π.Equiv π' → Nonempty ((jacquetRep F n γ π).Equiv (jacquetRep F n γ π')) := by
  intro F _ _ _ _ n γ V V' _ _ _ _ π π' φ
  let e : V ≃ₗ[ℂ] V' := φ.toLinearEquiv
  have he : ∀ g, (e : V →ₗ[ℂ] V') ∘ₗ π g = π' g ∘ₗ (e : V →ₗ[ℂ] V') := by
    intro g
    rw [Representation.Equiv.toLinearEquiv_toLinearMap]
    exact φ.toIntertwiningMap.isIntertwining' g
  have he' := LinearEquiv.isIntertwining_symm_isIntertwining he
  let f : Representation.IntertwiningMap (MonoidHom.comp π (unipotentRadical F n γ).subtype) (MonoidHom.comp π' (unipotentRadical F n γ).subtype) :=
    ⟨(e : V →ₗ[ℂ] V'), fun x => he x⟩
  let g : Representation.IntertwiningMap (MonoidHom.comp π' (unipotentRadical F n γ).subtype) (MonoidHom.comp π (unipotentRadical F n γ).subtype) :=
    ⟨(e.symm : V' →ₗ[ℂ] V), fun x => he' x⟩
  let M := Representation.Coinvariants.map _ _ f
  let M' := Representation.Coinvariants.map _ _ g
  have hMM' : M ∘ₗ M' = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.apply_symm_apply v
  have hM'M : M' ∘ₗ M = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.symm_apply_apply v
  let E := LinearEquiv.ofLinearMap (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids) M M' hMM' hM'M
  refine ⟨Representation.Equiv.mk E ?_⟩
  intro m
  apply Representation.Coinvariants.hom_ext
  ext u
  have hc : f ((π (m : GL (Fin n) F)) u) = (π' (m : GL (Fin n) F)) (f u) := LinearMap.congr_fun (he m) u
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.coe_ofLinearMap, jacquetRep,
    GroundTheory.Automorphic.Parabolic.twist_apply, map_smul, GroundTheory.Automorphic.Parabolic.jacquetAction,
    MonoidHom.coe_mk, OneHom.coe_mk, GroundTheory.Automorphic.coinvariantsTranslate_mk, M,
    Representation.Coinvariants.map_mk]
  rw [hc]

end GlobalTheory.CompanionTheory.JacquetEquiv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventually
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.KerSeq

variable {X : Scheme.{0}}

def secMap {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := fun r x => Scheme.Modules.Hom.app_smul _ _ _

theorem secMap_apply {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) (x : Γ(F, U)) :
    secMap φ U x = φ.app U x := rfl

theorem secMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (U : X.Opens) (x : Γ(F, U)) :
    secMap ψ U (secMap φ U x) = secMap (φ ≫ ψ) U x := by
  rw [secMap_apply, secMap_apply, secMap_apply, Scheme.Modules.Hom.comp_app]
  rfl

theorem isCoherent_copies {k : ℕ} {F : X.Modules} (hF : IsCoherent F) :
    IsCoherent (⨁ fun _ : Fin k => F) := by
  haveI : SheafOfModules.IsQuasicoherent F := hF.1
  refine And.intro (isQuasicoherent_biproduct _) fun U hU => ?_
  haveI : Module.Finite Γ(X, U) Γ(F, U) := hF.2 U hU
  let L : (Fin k → Γ(F, U)) →ₗ[Γ(X, U)] Γ(⨁ fun _ : Fin k => F, U) :=
    ∑ j, (secMap (biproduct.ι (fun _ : Fin k => F) j) U).comp (LinearMap.proj (R := Γ(X, U)) j)
  refine Module.Finite.of_surjective L fun m =>
    ⟨fun j => secMap (biproduct.π (fun _ : Fin k => F) j) U m, ?_⟩
  refine Eq.trans ?_ (biproduct_app_eq_sum (fun _ : Fin k => F) U m).symm
  simp only [L, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    secMap_apply]

variable {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}

theorem iSup_range_diagOp (h : OpSeq k M T d) (U : X.affineOpens) (e : ℕ) :
    ⨆ j, LinearMap.range (secMap (diagOp T d j e) (U : X.Opens)) = ⊤ := by
  have key : ∀ c : Fin k, ⊤ ≤ (⨆ j, LinearMap.range (secMap (diagOp T d j e) (U : X.Opens))).comap
      (secMap (biproduct.ι (fun _ : Fin k => M (d + e + 1)) c) (U : X.Opens)) := by
    intro c
    rw [← h.gen (d + e) (Nat.le_add_right d e) U]
    refine Submodule.span_le.mpr fun y hy => ?_
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hy
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem i (LinearMap.mem_range.mpr
      ⟨secMap (biproduct.ι (fun _ : Fin k => M (d + e)) c) (U : X.Opens) x, ?_⟩)
    rw [secMap_comp, ← secMap_apply (T i (d + e)), secMap_comp]
    rw [show biproduct.ι (fun _ : Fin k => M (d + e)) c ≫ diagOp T d i e =
        T i (d + e) ≫ biproduct.ι (fun _ : Fin k => M (d + e + 1)) c by
          unfold diagOp
          exact biproduct.ι_map _ _]
  rw [eq_top_iff]
  intro m _
  rw [biproduct_app_eq_sum (fun _ : Fin k => M (d + e + 1)) (U : X.Opens) m]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hc := Submodule.mem_comap.mp (key c (Submodule.mem_top
    (x := secMap (biproduct.π (fun _ : Fin k => M (d + e + 1)) c) (U : X.Opens) m)))
  rwa [secMap_apply, secMap_apply] at hc

theorem kerSeq_gen_bounded : GradedNoeth → ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (U : X.affineOpens), ∃ dU : ℕ, ∀ e, dU ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) = ⊤ := by
  intro hGN X _ k M T d h U
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have hfin : ∀ e, Module.Finite Γ(X, U) Γ(sumN M k d e, U) := fun e =>
    (isCoherent_copies (k := k) (h.coherent (d + e))).2 U U.2
  obtain ⟨d', hd'⟩ := hGN Γ(X, U) k (fun e => Γ(sumN M k d e, U))
    (fun j e => secMap (diagOp T d j e) (U : X.Opens))
    (fun i j e x => by
      rw [secMap_comp, secMap_comp, diagOp_comm T h.comm d i j e])
    0 (fun e _ => iSup_range_diagOp h U e)
    (fun e => LinearMap.range (secMap (kernel.ι (sumMap T d e)) (U : X.Opens)))
    (fun i e => by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
      refine LinearMap.mem_range.mpr ⟨secMap (kerOp T h.comm d i e) (U : X.Opens) x, ?_⟩
      rw [secMap_comp, secMap_comp, kerOp_ι])
  refine ⟨d', fun e he => ?_⟩
  have hd'' : ⨆ i, Submodule.map (secMap (diagOp T d i e) (U : X.Opens))
      (LinearMap.range (secMap (kernel.ι (sumMap T d e)) (U : X.Opens))) =
      LinearMap.range (secMap (kernel.ι (sumMap T d (e + 1))) (U : X.Opens)) := hd' e he
  have hinj : Function.Injective (secMap (kernel.ι (sumMap T d (e + 1))) (U : X.Opens)) :=
    GlobalTheory.QCoh.app_injective_of_mono _ _
  apply Submodule.map_injective_of_injective hinj
  have hS : Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) =
      ⨆ i, LinearMap.range (secMap (kerOp T h.comm d i e) (U : X.Opens)) := by
    rw [Submodule.iSup_eq_span]
    simp only [LinearMap.coe_range]
    rfl
  rw [hS, Submodule.map_iSup, Submodule.map_top, ← hd'']
  refine iSup_congr fun i => ?_
  rw [← LinearMap.range_comp, ← LinearMap.range_comp]
  congr 1
  ext x
  simp only [LinearMap.comp_apply]
  rw [secMap_comp, secMap_comp, kerOp_ι]

end GlobalTheory.CompanionTheory.GE.KerSeq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSequenceCoherent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

theorem isCoherent_biproduct {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → X.Modules) (hF : ∀ i, IsCoherent (F i)) : IsCoherent (⨁ F) := by
  haveI : ∀ i, SheafOfModules.IsQuasicoherent (F i) := fun i => (hF i).1
  refine ⟨isQuasicoherent_biproduct F, fun U hU => ?_⟩
  haveI : ∀ i, Module.Finite Γ(X, U) ((F i).presheaf.obj (Opposite.op U)) := fun i => (hF i).2 U hU
  let L : ∀ j, (F j).presheaf.obj (Opposite.op U) →ₗ[Γ(X, U)] (⨁ F).presheaf.obj (Opposite.op U) :=
    fun j =>
    { toFun := fun x => ConcreteCategory.hom (Scheme.Modules.Hom.app (biproduct.ι F j) U) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        exact Scheme.Modules.Hom.app_smul _ r x }
  let f : (∀ j, (F j).presheaf.obj (Opposite.op U)) →ₗ[Γ(X, U)] (⨁ F).presheaf.obj (Opposite.op U) :=
    ∑ j, (L j).comp (LinearMap.proj j)
  refine Module.Finite.of_surjective f ?_
  intro m
  refine ⟨fun j => ConcreteCategory.hom (Scheme.Modules.Hom.app (biproduct.π F j) U) m, ?_⟩
  rw [LinearMap.sum_apply]
  exact (biproduct_app_eq_sum F U m).symm

theorem isCoherent_kerSeq : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}, OpSeq k M T d →
    ∀ e, IsCoherent (KerSeq.kerSeq T d e) := by
  intro X _ k M T d h e
  haveI : SheafOfModules.IsQuasicoherent (M (d + e + 1)) := (h.coherent _).1
  exact isCoherent_kernel (KerSeq.sumMap T d e) (isCoherent_biproduct _ fun _ => h.coherent _)

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfPartsStatement
section
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_vector_formula_of_parts : Prop1 → Simil → Hasse → Cnt → E1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula | exact GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula | (intros; apply GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxHoldsStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_strong_approx_holds : Sa2.PropPlane := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.plane | exact GlobalTheory.CompanionTheory.PlaneSA.plane | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.plane <;> assumption)
end

