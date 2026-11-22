import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerSeparatedOfTrivialPowerCartesian
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private theorem kn_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N : ℕ} {k u : G.GAf}
    (hk : k ∈ L.KN 1) (hu : u ∈ L.KN N) : k * u * k⁻¹ ∈ L.KN N := by
  have key : ∀ g : G.GAf, L.CongOne 1 g → L.CongOne 1 g⁻¹ → ∀ x : G.GAf, L.CongOne N x →
      L.CongOne N (g * x * g⁻¹) := by
    intro g hg hg' x hx
    unfold Link.CongOne at hg hg' hx ⊢
    intro v hv
    obtain ⟨w₁, hw₁, h₁⟩ := hg' v hv
    have hv₁ : L.actG g⁻¹ v ∈ LaHat D := by
      rw [h₁, one_smul]
      exact add_mem hv hw₁
    obtain ⟨w₂, hw₂, h₂⟩ := hx _ hv₁
    obtain ⟨w₃, hw₃, h₃⟩ := hg w₂ hw₂
    refine ⟨w₂ + w₃, add_mem hw₂ hw₃, ?_⟩
    have hgg : L.actG g (L.actG g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₂, map_add, hgg, map_nsmul, h₃,
      one_smul]
  have hk' : L.CongOne 1 k ∧ L.CongOne 1 k⁻¹ := hk
  have hu' : L.CongOne N u ∧ L.CongOne N u⁻¹ := hu
  show L.CongOne N (k * u * k⁻¹) ∧ L.CongOne N (k * u * k⁻¹)⁻¹
  refine ⟨key k hk'.1 hk'.2 u hu'.1, ?_⟩
  have hinv : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
  rw [hinv]
  exact key k hk'.1 hk'.2 u⁻¹ hu'.2

private theorem gen_mono {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Mono (gen (Ow w) E) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (Ow w) E)) := IsLocalization.epi (nonZeroDivisors (Ow w)) E
  change Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (Ow w) E)).op)
  infer_instance

theorem UpperTheory.tower_separated_of_trivial_powerCartesian :
    PiZero → BaseSep → PowCart → PiSep := by
  intro hPZ hBS hPC p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C Ω _ _ z z' hz
  obtain ⟨ρ, e, hopen, -, htr⟩ := hPZ p D G L E gb w q r 𝔴 𝔫 S k T N c a hNum C
  have hKM := T.K_eq ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩
  revert hKM
  revert ρ
  generalize T.lev ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩ = M
  intro ρ e hopen htr hKM
  have x : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have y : ∀ u ∈ T.X.K (T.lev N), 1 * u * 1⁻¹ ∈ T.X.K M := fun u hu => by
    have hN : S.N₀ ∣ (N : ℕ) := ⟨c, hNum.1⟩
    have hu' : u ∈ L.KN S.N₀ := KN_anti hN (by rw [← T.K_eq]; exact hu)
    rw [hKM]
    simpa using hu'
  have htr' := htr x y
  have hzM : z ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ := by
    rw [htr', ← Category.assoc, hz, Category.assoc]
  have hzq : z ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M := by
    haveI : Mono (gen (Ow w) E) := gen_mono w
    rw [← cancel_mono (gen (Ow w) E)]
    simp only [Category.assoc]
    rw [← e]
    simp only [← Category.assoc] at hzM ⊢
    rw [hzM]
  have hzt : z ≫ T.X.tr (T.lev N) M 1 x y = z' ≫ T.X.tr (T.lev N) M 1 x y := by
    haveI := hopen
    rw [← cancel_mono (pullback.lift ρ (T.X.q M) e)]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact hzM
    · simp only [Category.assoc, pullback.lift_snd]
      exact hzq
  have hnorm : ∀ g ∈ T.X.K M, ∀ u ∈ T.X.K (T.lev N), g * u * g⁻¹ ∈ T.X.K (T.lev N) := by
    intro g hg u hu
    rw [hKM] at hg
    rw [T.K_eq] at hu ⊢
    exact kn_conj L (KN_anti (one_dvd _) hg) hu
  obtain ⟨g, hg, a', b', hz'⟩ := T.X.trans (T.lev N) M x y hnorm Ω z z' hzt
  refine ⟨g, ?_, a', b', hz'⟩
  rw [hKM] at hg
  obtain ⟨π, o, ψ, φ, hw, hπ, htrans, heq⟩ := T.tr_eq N N g a' b'
  have hP2 := (hPC _ _ _ (T.M N).univ.A (T.M N).univ.A (T.M N).univ.A π (𝟙 _) (Over.Hom.left ψ ≫ φ.φ)
    (𝟙 _) hw (by simp) k).2.1
  have hP3 : Cls.pw C k ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom = (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j :=
    (hPC _ _ _ (T.M N).univ.A S.Y.univ.A S.Y.univ.A C.j (𝟙 _) C.m.φ (𝟙 _) _ (by simp) k).2.1
  have h1 : z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom =
      z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ π := by
    rw [hz', Category.assoc, reassoc_of% heq, hP2]
  have h2 : z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j =
      z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j := by
    have hz2 := hz
    unfold Site.pi at hz2
    rw [← hP3]
    simp only [← Category.assoc] at hz2 ⊢
    rw [hz2]
  refine hBS p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N c a hNum C g hg ⟨π, o, ψ, φ, hπ, htrans⟩ Ω
    (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ?_
  show (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ π ≫ C.j =
    (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ C.j
  simp only [Category.assoc]
  rw [h2, reassoc_of% h1]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerTrivialOfQuotientTracePowerCartesian
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private lemma pullback_lift_clopen_immersion {W X Mη M P B B' Z : Scheme.{0}} (j : X ⟶ Mη) (f₁ : Mη ⟶ M) (f₂ : Mη ⟶ B') (s : M ⟶ B)
    (g : B' ⟶ B) (hp : IsPullback f₁ f₂ s g) (h : P ⟶ M) (w : W ⟶ X) (φ : W ⟶ P)
    (hc : IsPullback φ w h (j ≫ f₁)) (ε : Z ≅ W) (ρ : Z ⟶ P) (hρ : ρ = ε.hom ≫ φ) (t : Z ⟶ B')
    (ht : t = ε.hom ≫ w ≫ j ≫ f₂) (e : ρ ≫ h ≫ s = t ≫ g) [IsOpenImmersion j] [IsClosedImmersion j] :
    IsOpenImmersion (pullback.lift ρ t e) ∧ IsClosedImmersion (pullback.lift ρ t e) := by
  have hQ : IsPullback (pullback.fst (h ≫ s) g) (pullback.snd (h ≫ s) g) (h ≫ s) g :=
    IsPullback.of_hasPullback _ _
  have hu0 : (pullback.fst (h ≫ s) g ≫ h) ≫ s = pullback.snd (h ≫ s) g ≫ g := by
    rw [Category.assoc]; exact pullback.condition
  let u : pullback (h ≫ s) g ⟶ Mη := hp.lift (pullback.fst _ _ ≫ h) (pullback.snd _ _) hu0
  have hu1 : u ≫ f₁ = pullback.fst _ _ ≫ h := hp.lift_fst _ _ _
  have hu2 : u ≫ f₂ = pullback.snd _ _ := hp.lift_snd _ _ _
  have A : IsPullback u (pullback.fst (h ≫ s) g) f₁ h :=
    IsPullback.of_right (h₁₂ := f₂) (v₁₃ := g) (h₂₂ := s) (by rw [hu2]; exact hQ.flip) hu1 hp.flip
  have hφ : φ ≫ h ≫ s = (w ≫ j ≫ f₂) ≫ g := by
    rw [← Category.assoc, hc.w]
    simp only [Category.assoc, hp.w]
  let l : W ⟶ pullback (h ≫ s) g := pullback.lift φ (w ≫ j ≫ f₂) hφ
  have hl1 : l ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hl2 : l ≫ pullback.snd _ _ = w ≫ j ≫ f₂ := pullback.lift_snd _ _ _
  have hlu : l ≫ u = w ≫ j := by
    apply hp.hom_ext
    · rw [Category.assoc, hu1, ← Category.assoc, hl1, hc.w, Category.assoc]
    · rw [Category.assoc, hu2, hl2, Category.assoc]
  have B1 : IsPullback l w u j :=
    IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := h) (h₂₂ := f₁) (by rw [hl1]; exact hc) hlu A.flip
  have o1 : IsOpenImmersion l := MorphismProperty.of_isPullback (P := @IsOpenImmersion) B1.flip inferInstance
  have o2 : IsClosedImmersion l := MorphismProperty.of_isPullback (P := @IsClosedImmersion) B1.flip inferInstance
  have hE : pullback.lift ρ t e = ε.hom ≫ l := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hl1, hρ]
    · rw [pullback.lift_snd, Category.assoc, hl2, ht]
  rw [hE]
  exact ⟨inferInstance, inferInstance⟩

private lemma powMap_congr {S' S₁ : Scheme.{0}} {A' : Over S'} {A : Over S₁} {f f' : S' ⟶ S₁} {φ φ' : A'.left ⟶ A.left}
    (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f) (h' : φ' ≫ A.hom = A'.hom ≫ f') (m : ℕ) :
    GlobalTheory.KS.powMap f φ h m = GlobalTheory.KS.powMap f' φ' h' m := by
  subst hf; subst hφ; rfl

theorem UpperTheory.tower_trivial_of_quotient_trace_powerCartesian :
    MIn → QObj → QComp → QIso → QUniq → TrEta → TrUnit → PowCart → PiZero := by
  intro hM hQO hQC hQI hQU hTE hTU hPC p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T N c a hNum C
  haveI : IsNoetherianRing (Ow w) := inferInstance
  let N₀' : Lv p := ⟨S.N₀, S.std.three, S.cop⟩
  let β : Ow w →+* E := algebraMap (Ow w) E
  obtain ⟨j₀, hop, hcl, hj, φA, φ₂, hcart, hsq, hact, ⟨hpol⟩, heta⟩ :=
    hM.cmp q (datAt S.atq S.sp) (Ow w) S.b E β gb S.mat.1 S.mat.2 S.N₀ S.std.three S.std.cop S.M (T.M N₀')
  let f₀ : (T.M N₀').X ⟶ S.M.X := j₀ ≫ pullback.fst _ _
  let n₀ : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N₀').univ S.M.univ f₀ 1 :=
    { φ := φA, φ₂ := φ₂, cart := hcart, sq := hsq, act := hact, pol := hpol,
      eta := fun y => by rw [one_smul]; exact heta y }
  let pw := GlobalTheory.KS.powMap f₀ n₀.φ n₀.cart.1.w k
  have pc := hPC _ _ _ (T.M N₀').univ.A S.M.univ.A S.M.univ.A f₀ (𝟙 _) n₀.φ (𝟙 _) n₀.cart.1.w (by simp) k
  have hs : f₀ ≫ S.M.s = (T.M N₀').s ≫ spMap β := by
    simp only [f₀, Category.assoc]
    rw [pullback.condition, ← Category.assoc, hj]
  have hq : T.X.q (T.lev N₀') = (T.e N₀').hom ≫ (GlobalTheory.KS.pow (T.M N₀').univ.A k).hom ≫ j₀ ≫ pullback.snd _ _ := by
    rw [hj, T.e_q]
  have e : ((T.e N₀').hom ≫ pw) ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s = T.X.q _ ≫ gen (Ow w) E := by
    rw [← T.e_q N₀']
    simp only [Category.assoc]
    rw [← Category.assoc pw, pc.2.1]
    simp only [Category.assoc]
    rw [hs]
  refine ⟨(T.e N₀').hom ≫ pw, e, ?_⟩
  haveI := hop
  haveI := hcl
  obtain ⟨h1, h2⟩ := pullback_lift_clopen_immersion j₀ (pullback.fst _ _) (pullback.snd _ _) S.M.s (spMap β)
    (IsPullback.of_hasPullback _ _) (GlobalTheory.KS.pow S.M.univ.A k).hom (GlobalTheory.KS.pow (T.M N₀').univ.A k).hom pw
    (pc.1 n₀.cart.1) (T.e N₀') _ rfl _ hq e
  refine ⟨h1, h2, fun x y => ?_⟩
  obtain ⟨π, o, ψ, φ, hw, hπs, htrans, htr⟩ := T.tr_eq N N₀' 1 x y
  obtain ⟨hiso, hlb⟩ := hTU p D G L E gb 1 _ _ N N₀' (T.M N).univ o ψ htrans (one_mem _)
  have heta' : ∀ y' : D.La, (T.M N).univ.eta (c • y') ≫ ψ = o.eta (1 • y') := fun y' =>
    hTE p D G L E gb 1 _ _ N N₀' (T.M N).univ o ψ htrans S.N₀ c 1 hNum.1 (_root_.mul_one _).symm y' y'
      ⟨0, zero_mem _, by simp⟩
  obtain ⟨n₁, hn₁⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb S.N₀ S.N₀ 1 _ _ _ (T.M N₀').s S.M.s S.M.s (T.M N₀').univ
    S.M.univ S.M.univ f₀ (𝟙 _)).2.2.2 _ (T.M N).s o π φ n₀
  obtain ⟨n₂, hn₂⟩ := hQI q (datAt S.atq S.sp) (Ow w) E S.b gb S.N₀ N.1 S.N₀ 1 c _ _ (T.M N).s S.M.s (T.M N).univ o
    S.M.univ (π ≫ f₀) ψ hiso htrans.1 htrans.2.1 hlb heta' n₁
  obtain ⟨n₃, hn₃⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c _ _ _ (T.M N).s S.Y.s S.M.s (T.M N).univ
    S.Y.univ S.M.univ C.j S.π).1 C.m S.mπ
  obtain ⟨o₀, ⟨n₄⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb β S.mat N.1 S.N₀ c hNum.1 (by have := N.2.1; omega)
    S.std.cop _ (T.M N).s (T.M N).univ
  obtain ⟨f', -, huniq⟩ := S.M.rep _ ((T.M N).s ≫ spMap β) o₀
  have key : ∀ (g : (T.M N).X ⟶ S.M.X), QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ g c →
      g ≫ S.M.s = (T.M N).s ≫ spMap β → g = f' := by
    intro g n hg
    have n' : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ (𝟙 _ ≫ g) c := by
      rw [Category.id_comp]; exact n
    obtain ⟨m, -⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c _ _ _ (T.M N).s _ S.M.s (T.M N).univ
      o₀ S.M.univ (𝟙 _) g).2.2.1 inferInstance n₄ n'
    exact huniq g ⟨hg, ⟨m⟩⟩
  have hf : C.j ≫ S.π = π ≫ f₀ := by
    rw [key _ n₃ ?_, key _ n₂ ?_]
    · rw [Category.assoc, hs, ← Category.assoc, hπs]
    · rw [Category.assoc, S.ov, C.ov]
  have cast : ∀ {f f' : (T.M N).X ⟶ S.M.X} (_ : f = f')
      (n : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ f c),
      ∃ n' : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ f' c, n'.φ = n.φ := by
    intro f f' hff n
    subst hff
    exact ⟨n, rfl⟩
  obtain ⟨n₅, hn₅⟩ := cast hf n₃
  have hφ : C.m.φ ≫ S.mπ.φ = (ψ.left ≫ φ.φ) ≫ n₀.φ := by
    rw [← hn₃, ← hn₅, hQU q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c S.std.three S.std.cop _ _ (T.M N).s S.M.s
      (T.M N).univ S.M.univ (π ≫ f₀) n₅ n₂, hn₂, hn₁, Category.assoc]
  have hv1 : ((ψ.left ≫ φ.φ) ≫ n₀.φ) ≫ S.M.univ.A.hom = (T.M N).univ.A.hom ≫ π ≫ f₀ := by
    rw [Category.assoc, n₀.cart.1.w, ← Category.assoc, hw, Category.assoc]
  have hv2 : (C.m.φ ≫ S.mπ.φ) ≫ S.M.univ.A.hom = (T.M N).univ.A.hom ≫ C.j ≫ S.π := by
    rw [Category.assoc, S.mπ.cart.1.w, ← Category.assoc, C.m.cart.1.w, Category.assoc]
  have c1 := (hPC _ _ _ (T.M N).univ.A (T.M N₀').univ.A S.M.univ.A π f₀ (ψ.left ≫ φ.φ) n₀.φ hw n₀.cart.1.w k).2.2 hv1
  have c2 := (hPC _ _ _ (T.M N).univ.A S.Y.univ.A S.M.univ.A C.j S.π C.m.φ S.mπ.φ C.m.cart.1.w S.mπ.cart.1.w k).2.2 hv2
  change T.X.tr (T.lev N) (T.lev N₀') 1 x y ≫ (T.e N₀').hom ≫ pw =
    ((T.e N).hom ≫ GlobalTheory.KS.powMap C.j C.m.φ C.m.cart.1.w k) ≫ GlobalTheory.KS.powMap S.π S.mπ.φ S.mπ.cart.1.w k
  rw [← Category.assoc, htr, Category.assoc, Category.assoc, c1, c2]
  exact congrArg _ (powMap_congr hf.symm hφ.symm hv1 hv2 k)
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaIdentity
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

private theorem sec_eq_of_points {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (n : ℕ) (hn : IsUnit (n : Γ(X, ⊤))) (σ σ' : 𝟙_ (Over X) ⟶ A) (h₁ : σ ^ n = 1) (h₂ : σ' ^ n = 1)
    (hpt : ∀ q : X, ∃ (k : Type) (_ : Field k) (y : Sp k ⟶ X), q ∈ Set.range y ∧
      toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ σ') : σ = σ' := by
  have key : ∀ q : X, ∃ V : X.Opens, q ∈ V ∧ V.ι ≫ σ.left = V.ι ≫ σ'.left := by
    intro q
    obtain ⟨k, hk, y, ⟨z, hz⟩, he⟩ := hpt q
    obtain ⟨V, hV, hVe⟩ := GlobalTheory.UPel.LocSim.exists_open_eq_of_torsion_point X A hA n hn σ σ' h₁ h₂ k y he
    exact ⟨V, hV ⟨z, hz⟩, hVe⟩
  choose V hV hVe using key
  have hcov : TopologicalSpace.IsOpenCover V := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun q _ => ?_)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨q, hV q⟩
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover V hcov) _ _ fun q => hVe q

private theorem map_nsmul_pow {M Q : Type} [AddCommGroup M] [Group Q] (f : M → Q) (hf : ∀ a b, f (a + b) = f a * f b)
    (m : ℕ) (a : M) : f (m • a) = f a ^ m := by
  induction m with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := f 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ m ih =>
    rw [succ_nsmul, hf, ih, pow_succ]

private theorem pow_comp_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {T A B : C} [GrpObj A] [GrpObj B]
    (a : T ⟶ A) (ψ : A ⟶ B) [IsMonHom ψ] (m : ℕ) : (a ≫ ψ) ^ m = (a ^ m) ≫ ψ := (map_pow (IsMonHom.monoidHom ψ T) a m).symm

private theorem ev_tower {G : GDatum} {k Q : Type} [Field k] [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso G k Q act e) {M n c : ℕ} (hM : M = n * c) (hn : 0 < n) (hc : 0 < c) (z : G.La) :
    I.ev M (c • z) = I.ev n z := by
  subst hM
  rw [map_nsmul_pow (I.ev _) (I.add _)]
  exact I.tower n c hn hc z

theorem UpperTheory.trace_eta_identity : UpperTheory.Gal.Int.Geo.TrEta := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT n c' c hN' hN x y hxy
  haveI : IsMonHom ψ := hT.1
  have h3' := N'.2.1
  have h3 := N.2.1
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hN'; omega)
  have hc' : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN'; omega)
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN; omega)
  have hcop : n.Coprime p := Nat.Coprime.coprime_dvd_left ⟨c', hN'⟩ N'.2.2
  have hunit : IsUnit (n : Γ(X, ⊤)) := by
    have hR : IsUnit (n : R) := by
      have hq : IsUnit (n : ℚ) := (Nat.cast_ne_zero.mpr hn.ne').isUnit
      simpa using hq.map (algebraMap ℚ R)
    have := hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using this
  have ex' : (n • c' • x : D.La) = (↑N' : ℕ) • x := by rw [smul_smul, ← hN']
  have ex : (n • c • y : D.La) = (↑N : ℕ) • y := by rw [smul_smul, ← hN]
  have e1 : (o'.eta (c' • x)) ^ n = 1 :=
    (map_nsmul_pow o'.eta o'.eta_add n (c' • x)).symm.trans ((congrArg o'.eta ex').trans (o'.eta_ker x))
  have hpow1 : (o'.eta (c' • x) ≫ ψ) ^ n = 1 :=
    (pow_comp_hom _ _ _).trans ((congrArg (· ≫ ψ) e1).trans (map_one (IsMonHom.monoidHom ψ _)))
  have hpow2 : (o.eta (c • y)) ^ n = 1 :=
    (map_nsmul_pow o.eta o.eta_add n (c • y)).symm.trans ((congrArg o.eta ex).trans (o.eta_ker y))
  refine sec_eq_of_points o.A o.ab n hunit _ _ hpow1 hpow2 (fun q => ?_)
  let κ := X.residueField q
  let k := AlgebraicClosure κ
  let y0 : Sp k ⟶ X := spMap (algebraMap κ k) ≫ X.fromSpecResidueField q
  let β : R →+* k := (Spec.preimage (y0 ≫ s)).hom
  have hβ : y0 ≫ s = spMap β := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (y0 ≫ s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨I', I'', hI', hI'', hiff⟩ := hT.2.2.2.2 k y0 β hβ
  refine ⟨k, inferInstance, y0, ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply q _⟩, ?_⟩
  calc toUnit (Over.mk y0) ≫ (o'.eta (c' • x) ≫ ψ)
      = (toUnit (Over.mk y0) ≫ o'.eta (c' • x)) ≫ ψ := (Category.assoc _ _ _).symm
    _ = I'.ev (↑N') (c' • x) ≫ ψ := congrArg (· ≫ ψ) (hI' _)
    _ = I'.ev n x ≫ ψ := congrArg (· ≫ ψ) (ev_tower I' hN' hn hc' x)
    _ = I''.ev n y := (hiff n hn hcop x y).mpr hxy
    _ = I''.ev (↑N) (c • y) := (ev_tower I'' hN hn hc y).symm
    _ = toUnit (Over.mk y0) ≫ o.eta (c • y) := (hI'' _).symm
end
end

