import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLatIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.LatticeIsomorphism

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem rd_add (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (u v : VQ D) :
    rd L x h (u + v) = rd L x h u + rd L x h v := by
  simp only [rd, TensorProduct.tmul_add, map_add]

private noncomputable def rdHom (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) : VQ D →+ AfP p ⊗[ℚ] VQ D :=
  AddMonoidHom.mk' (rd L x h) (rd_add L x h)

private theorem rd_sub (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (u v : VQ D) :
    rd L x h (u - v) = rd L x h u - rd L x h v := by
  exact map_sub (rdHom L x h) u v

private theorem rd_nsmul (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (n : ℕ) (u : VQ D) :
    rd L x h (n • u) = n • rd L x h u := by
  exact map_nsmul (rdHom L x h) n u

private theorem actY_inv {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y (actY L y⁻¹ w) = w := by
  show L.rep _ (L.rep _ w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private theorem inv_actY {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y⁻¹ (actY L y w) = w := by
  show L.rep ((y⁻¹ : GlobalTheory.LKCx.grp G β) : G.Cˣ × ℚˣ).1 (L.rep ((y : G.Cˣ × ℚˣ).1 : G.C) w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private noncomputable def placeY {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv} (j'' : D''.La →+ VQ D) :
    D''.La →+ VQ D :=
  (LinearMap.toAddMonoidHom (actY L y)).comp j''

private theorem placeY_apply {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv} (j'' : D''.La →+ VQ D)
    (u : D''.La) : placeY L y j'' u = actY L y (j'' u) := rfl

private theorem coordA_placeY (hR : RdAct) (B : GlobalTheory.LKCx.Form G) (y : GlobalTheory.LKCx.grp G B.β) {N : ℕ}
    {D'' : PLat D.O D.inv} {t'' : D.La → D''.La} {j'' : D''.La →+ VQ D} {h : G.GAf}
    (hc : IsCoordA L (trivX B) N D'' t'' j'' h) :
    IsCoordA L (trivX B) N D'' t'' (placeY L y j'') (B.toAf y * h) := by
  have key : ∀ w, rd L (trivX B) (B.toAf y * h) (actY L y w) = rd L (trivX B) h w := by
    intro w
    rw [hR p D G L B y (B.toAf y * h) h w]
    have e : (B.toAf y * h)⁻¹ * B.toAf y * h = 1 := by group
    rw [e, map_one, Module.End.one_apply]
  refine ⟨fun w => ?_, fun a => ?_⟩
  · have hw : w = actY L y (actY L y⁻¹ w) := (actY_inv L y w).symm
    rw [hw, key, ← hc.1 (actY L y⁻¹ w), ← hw]
    constructor
    · rintro ⟨r, u, hu⟩
      refine ⟨r, u, ?_⟩
      rw [placeY_apply] at hu
      rw [← map_nsmul, hu, inv_actY]
    · rintro ⟨r, u, hu⟩
      refine ⟨r, u, ?_⟩
      rw [placeY_apply, ← hu, map_nsmul, actY_inv]
  · obtain ⟨w1, hw1, e⟩ := hc.2 a
    exact ⟨w1, hw1, by rw [placeY_apply, key, e]⟩

private theorem locP_placeY {β : G.Cˣ} (PD : PDic L β) (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv}
    {j'' : D''.La →+ VQ D} {hp : Gr G 1} (hl : IsLocP D'' j'' (PD.lat hp)) :
    IsLocP D'' (placeY L y j'') (PD.lat (GlobalTheory.LKCx.toP1 G β y * hp)) := by
  intro w
  have hw : w = actY L y (actY L y⁻¹ w) := (actY_inv L y w).symm
  rw [hw, PD.equiv y hp, ← hl (actY L y⁻¹ w), ← hw]
  constructor
  · rintro ⟨m, u, hm, hu⟩
    refine ⟨m, u, hm, ?_⟩
    rw [placeY_apply] at hu
    rw [← map_nsmul, hu, inv_actY]
  · rintro ⟨m, u, hm, hu⟩
    refine ⟨m, u, hm, ?_⟩
    rw [placeY_apply, ← hu, map_nsmul, actY_inv]

private theorem range_le {x : (AfP p ⊗[ℚ] G.C)ˣ} {N : ℕ} {D₁ D₂ : PLat D.O D.inv} {t₁ : D.La → D₁.La}
    {t₂ : D.La → D₂.La} {j₁ : D₁.La →+ VQ D} {j₂ : D₂.La →+ VQ D} {h : G.GAf} {M : AddSubgroup (VQ D)}
    (hc₁ : IsCoordA L x N D₁ t₁ j₁ h) (hc₂ : IsCoordA L x N D₂ t₂ j₂ h)
    (hl₁ : IsLocP D₁ j₁ M) (hl₂ : IsLocP D₂ j₂ M) (u : D₁.La) : ∃ u₂, j₂ u₂ = j₁ u := by
  obtain ⟨r, u₂, hu₂⟩ := (hc₂.1 (j₁ u)).2 ((hc₁.1 (j₁ u)).1 ⟨0, u, by simp⟩)
  obtain ⟨m, u₃, hm, hu₃⟩ := (hl₂ (j₁ u)).2 ((hl₁ (j₁ u)).1 ⟨1, u, Nat.coprime_one_left p, one_smul _ _⟩)
  have hcop : IsCoprime ((p ^ r : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left r hm.symm)
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a • u₂ + b • u₃, ?_⟩
  calc j₂ (a • u₂ + b • u₃) = a • j₂ u₂ + b • j₂ u₃ := by rw [map_add, map_zsmul, map_zsmul]
    _ = (a * ((p ^ r : ℕ) : ℤ) + b * (m : ℤ)) • j₁ u := by
      rw [← hu₂, ← hu₃, add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul]
    _ = j₁ u := by rw [hab, one_smul]

private theorem mark_div {x : (AfP p ⊗[ℚ] G.C)ˣ} {N : ℕ} (hN0 : 0 < N) (hNp : N.Coprime p) {D₁ : PLat D.O D.inv}
    {j : D₁.La →+ VQ D} (hj : Function.Injective j) {h : G.GAf}
    (hc : ∀ w, (∃ (r : ℕ) (u : D₁.La), p ^ r • w = j u) ↔ rd L x h w ∈ LaHat D)
    (d : D₁.La) {w₃ : AfP p ⊗[ℚ] VQ D} (hw₃ : w₃ ∈ LaHat D) (hd : rd L x h (j d) = N • w₃) :
    ∃ e : D₁.La, d = N • e := by
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
  set w : VQ D := (N : ℚ)⁻¹ • j d with hwdef
  have hNw : N • w = j d := by
    rw [hwdef, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hN, one_smul]
  have e : rd L x h w = w₃ := by
    have h1 : (N : ℚ) • rd L x h w = (N : ℚ) • w₃ := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← rd_nsmul, hNw, hd]
    have h2 := congrArg (fun z => (N : ℚ)⁻¹ • z) h1
    simpa only [smul_smul, inv_mul_cancel₀ hN, one_smul] using h2
  obtain ⟨r, u, hu⟩ := (hc w).2 (e ▸ hw₃)
  have h3 : j (p ^ r • d) = j (N • u) := by
    rw [map_nsmul, map_nsmul, ← hNw, ← hu, smul_comm]
  have h4 := hj h3
  have hcop : IsCoprime (N : ℤ) ((p ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right r hNp)
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a • d + b • u, ?_⟩
  calc d = (a * (N : ℤ) + b * ((p ^ r : ℕ) : ℤ)) • d := by rw [hab, one_smul]
    _ = N • (a • d + b • u) := by
      rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, h4, smul_add, smul_comm N a d,
        smul_comm N b u]

end UpperTheory.Gal.W2.LatticeIsomorphism

open UpperTheory.Gal.W2.LatticeIsomorphism

theorem UpperTheory.Gal.W2.latIso_of :
    UpperTheory.Gal.W2.RdAct → UpperTheory.Gal.W2.CoordKN → UpperTheory.Gal.W2.ClsScalar → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.LatIso := by
  intro hR hK hS hA p _ D G L B PD N hN hNp D' t D'' t'' j j'' a a'' N₁ N₂ t₁ t₂ hc₁ hc₂ hpl hpl'' hca hca''
    hlp hlp'' y
  have hcaY : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') (B.toAf y * a''.1) := coordA_placeY L hR B y hca''
  have hlpY : IsLocP D'' (placeY L y j'') (PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2)) := locP_placeY L PD y hlp''
  constructor
  · rintro ⟨hm1, hm2⟩
    have hcaY' : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') a.1 :=
      (hK p D G L (trivX B) N hN hNp D'' t'' (placeY L y j'') _ _ hcaY).2 (by rwa [← _root_.mul_assoc])
    have hlat : PD.lat a.2 = PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2) :=
      (PD.inj _ _).2 (by rwa [← _root_.mul_assoc])
    have hlpY' : IsLocP D'' (placeY L y j'') (PD.lat a.2) := by
      rw [hlat]
      exact hlpY
    have hex : ∀ u : D''.La, ∃ u', j u' = placeY L y j'' u := range_le L hcaY' hca hlpY' hlp
    have hex' : ∀ u' : D'.La, ∃ u, placeY L y j'' u = j u' := range_le L hca hcaY' hlp hlpY'
    choose f hf using hex
    have hinj := hpl.1
    have hadd : ∀ u v, f (u + v) = f u + f v := fun u v => hinj (by simp only [map_add, hf])
    have hsmul : ∀ (c : D.O) u, f (c • u) = c • f u := fun c u => hinj (by
      rw [hf, hpl.2.1, hf, placeY_apply, placeY_apply, hpl''.2.1, (hA p D G L B.β y).2.1])
    let fl : D''.La →ₗ[D.O] D'.La := { toFun := f, map_add' := hadd, map_smul' := hsmul }
    have hYinj : Function.Injective (placeY L y j'') := by
      intro u v huv
      rw [placeY_apply, placeY_apply] at huv
      have e := congrArg (actY L y⁻¹) huv
      rw [inv_actY, inv_actY] at e
      exact hpl''.1 e
    have hbij : Function.Bijective fl := by
      refine ⟨fun u v huv => hYinj ?_, fun u' => ?_⟩
      · rw [← hf, ← hf]
        exact congrArg j huv
      · obtain ⟨u, hu⟩ := hex' u'
        exact ⟨u, hinj ((hf u).trans hu)⟩
    let w := LinearEquiv.ofBijective fl hbij
    have hjw : ∀ u, j (w u) = actY L y (j'' u) := fun u => hf u
    obtain ⟨s, hs, hsf⟩ := hpl.2.2.2
    obtain ⟨s'', hs'', hsf''⟩ := hpl''.2.2.2
    have hy2 : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    have hsc : ∀ u u' : D''.La, (((D'.EF (w u)) (w u') : ℤ) : ℚ) =
        s * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) / s'' * (((D''.EF u) u' : ℤ) : ℚ) := by
      intro u u'
      rw [hsf, hjw, hjw, (hA p D G L B.β y).1, hsf'']
      field_simp
    have hr := hS p D N₁ N₂ D' t₁ D'' t₂ hc₁ hc₂ w.toAddEquiv _ (by positivity) hsc
    have hiso : IsIsom D'' D' w := by
      intro u u'
      have e := hsc u u'
      rw [hr, _root_.one_mul] at e
      exact_mod_cast e
    refine ⟨w, ⟨hiso, fun a0 => ?_⟩, hjw⟩
    obtain ⟨w1, hw1, e1⟩ := hca.2 a0
    obtain ⟨w2, hw2, e2⟩ := hcaY'.2 a0
    have hd : rd L (trivX B) a.1 (j (w (t'' a0) - t a0)) = N • (w2 - w1) := by
      rw [map_sub, rd_sub, hjw, ← placeY_apply, e2, e1, smul_sub]
      abel
    obtain ⟨e, he⟩ := mark_div L hN hNp hinj hca.1 _ (sub_mem hw2 hw1) hd
    exact ⟨e, eq_add_of_sub_eq' he⟩
  · rintro ⟨w, ⟨hiso, hmark⟩, hjw⟩
    have hjY : ∀ u, placeY L y j'' u = j (w u) := fun u => (hjw u).symm
    have hcaY' : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') a.1 := by
      refine ⟨fun w0 => ?_, fun a0 => ?_⟩
      · rw [← hca.1 w0]
        constructor
        · rintro ⟨r, u, hu⟩
          exact ⟨r, w u, by rw [hu, hjY]⟩
        · rintro ⟨r, u, hu⟩
          exact ⟨r, w.symm u, by rw [hu, hjY, LinearEquiv.apply_symm_apply]⟩
      · obtain ⟨e, he⟩ := hmark a0
        obtain ⟨w1, hw1, e1⟩ := hca.2 a0
        have he' : rd L (trivX B) a.1 (j e) ∈ LaHat D := (hca.1 (j e)).1 ⟨0, e, by simp⟩
        refine ⟨w1 + rd L (trivX B) a.1 (j e), add_mem hw1 he', ?_⟩
        rw [hjY, he, map_add, map_nsmul, rd_add, rd_nsmul, e1, smul_add, add_assoc]
    have hkn := (hK p D G L (trivX B) N hN hNp D'' t'' (placeY L y j'') _ _ hcaY).1 hcaY'
    have hlpY' : IsLocP D'' (placeY L y j'') (PD.lat a.2) := by
      intro w0
      rw [← hlp w0]
      constructor
      · rintro ⟨m, u, hm, hu⟩
        exact ⟨m, w u, hm, by rw [hu, hjY]⟩
      · rintro ⟨m, u, hm, hu⟩
        exact ⟨m, w.symm u, hm, by rw [hu, hjY, LinearEquiv.apply_symm_apply]⟩
    have hlat : PD.lat a.2 = PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2) := by
      ext w0
      rw [← hlpY' w0, ← hlpY w0]
    have hkh := (PD.inj _ _).1 hlat
    exact ⟨by rw [_root_.mul_assoc]; exact hkn, by rw [_root_.mul_assoc]; exact hkh⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PMinBridge
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.minBridge_of :
    UpperTheory.Gal.W2.MinBridge := by
  intro p _ D G L β D' j hP ga c hga
  obtain ⟨hinj, hsmul, hspan, -⟩ := hP
  set f : 𝓞 D.F →+* G.F := (L.e : D.F →+* G.F).comp (algebraMap (𝓞 D.F) D.F) with hf
  have hpow : ∀ (n : ℕ) (u : D'.La), j ((ga ^ n) u) = (L.rep c ^ n) (j u) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ, Module.End.mul_apply, ih, hga, pow_succ, Module.End.mul_apply]
  have key : ∀ (q : (𝓞 D.F)[X]) (u : D'.La),
      j (q.sum fun i b => algebraMap (𝓞 D.F) D.O b • (ga ^ i) u) =
        L.rep (aeval c (q.map f)) (j u) := by
    intro q u
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      Polynomial.sum_def, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, hpow, map_mul, map_pow, Module.End.mul_apply, ← L.rep_F]
    rfl
  have hK : ∀ q : (𝓞 D.F)[X], Kills (algebraMap (𝓞 D.F) D.O) ga q ↔ aeval c (q.map f) = 0 := by
    intro q
    constructor
    · intro h
      apply L.rep_inj
      rw [map_zero]
      refine LinearMap.ext fun w => ?_
      obtain ⟨m, u, hm, hmu⟩ := hspan w
      have h1 : L.rep (aeval c (q.map f)) (j u) = 0 := by rw [← key, h u, map_zero]
      have h2 : m • L.rep (aeval c (q.map f)) w = 0 := by
        rw [← LinearMap.map_smul_of_tower, hmu, h1]
      rw [← Nat.cast_smul_eq_nsmul ℚ] at h2
      rw [LinearMap.zero_apply]
      exact (smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hm)
    · intro h x
      apply hinj
      rw [key, h, map_zero, LinearMap.zero_apply, map_zero]
  refine ⟨(minpoly.monic (Algebra.IsIntegral.isIntegral c)).map _, fun q => ?_⟩
  have hcomp : (L.e.symm : G.F →+* D.F).comp f = algebraMap (𝓞 D.F) D.F := by
    ext b
    simp [hf]
  rw [hK, ← minpoly.dvd_iff, ← map_dvd_iff (Polynomial.mapEquiv L.e.symm),
    Polynomial.mapEquiv_apply, Polynomial.mapEquiv_apply, Polynomial.map_map, hcomp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlaceLoc
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem formB_add_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (a b c : VQ D) : formB L β (a + b) c = formB L β a c + formB L β b c := by
  simp only [formB, map_add, LinearMap.add_apply]

private theorem formB_nsmul_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℕ) (a c : VQ D) : formB L β (n • a) c = n * formB L β a c := by
  simp only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]

private theorem formB_add_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (a b c : VQ D) : formB L β a (b + c) = formB L β a b + formB L β a c := by
  simp only [formB, map_add]

private theorem formB_nsmul_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℕ) (a c : VQ D) : formB L β a (n • c) = n * formB L β a c := by
  simp only [formB, map_nsmul, nsmul_eq_mul]

private theorem formB_zsmul_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℤ) (a c : VQ D) : formB L β a (n • c) = n * formB L β a c := by
  simp only [formB, map_zsmul, zsmul_eq_mul]

private theorem den_dvd_of_mul_eq_int (q : ℚ) (n : ℕ) (z : ℤ) (h : (n : ℚ) * q = z) : q.den ∣ n := by
  have h1 : (n : ℤ) * q.num = z * q.den := by
    have h2 : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    have h3 : (((n : ℤ) * q.num : ℤ) : ℚ) = ((z * q.den : ℤ) : ℚ) := by
      push_cast
      rw [h2, ← _root_.mul_assoc, h]
    exact_mod_cast h3
  have h3 : (q.den : ℤ) ∣ n * q.num := ⟨z, by rw [h1]; ring⟩
  have h4 : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  exact Int.natCast_dvd_natCast.1 (h4.dvd_of_dvd_mul_right h3)

theorem placeLoc_of : PlaceLoc := by
  intro p _ D G L β D' j hP hH
  obtain ⟨-, hact, hspan, s0, hs0, hform⟩ := hP
  obtain ⟨E₁, hE, e, he, hperf⟩ := hH
  have hE1 : ∀ u u', (E₁ u u' : ℚ) = (s0 / 2) * formB L β (j u) (j u') := by
    intro u u'
    have h := hform u u'
    rw [hE] at h
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    push_cast at h
    linarith
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ D'.La).FG)
  have hcl0 : AddSubgroup.closure (S : Set D'.La) = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hu : u ∈ Submodule.span ℤ (S : Set D'.La) := hS ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)
    | smul a x _ hx => exact zsmul_mem (hx trivial) a
  have hcl : AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) = j.range := by
    rw [Finset.coe_image, ← AddMonoidHom.map_closure, hcl0, AddMonoidHom.range_eq_map]
  let M : AddSubgroup (VQ D) :=
    { carrier := {w | ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u}
      add_mem' := by
        rintro a b ⟨m, u, hm, hu⟩ ⟨m', u', hm', hu'⟩
        refine ⟨m * m', m' • u + m • u', hm.mul_left hm', ?_⟩
        rw [map_add, map_nsmul, map_nsmul, ← hu, ← hu', smul_add, smul_smul, smul_smul, mul_comm m' m]
      zero_mem' := ⟨1, 0, Nat.coprime_one_left p, by simp⟩
      neg_mem' := by
        rintro a ⟨m, u, hm, hu⟩
        exact ⟨m, -u, hm, by rw [map_neg, ← hu, smul_neg]⟩ }
  have hM : ∀ w, w ∈ M ↔ ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u := fun w => Iff.rfl
  refine ⟨M, ⟨?_, S.image j, ?_, ?_⟩, ⟨s0 / 2, by positivity, ?_⟩, fun w => (hM w).symm⟩
  · rintro c w ⟨m, u, hm, h⟩
    exact ⟨m, c • u, hm, by rw [hact, ← h, map_nsmul]⟩
  · rw [eq_top_iff]
    intro w _
    obtain ⟨m, u, hm, h⟩ := hspan w
    have hu : j u ∈ AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) := hcl ▸ ⟨u, rfl⟩
    have hu' : j u ∈ Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D)) :=
      (AddSubgroup.closure_le (Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D))).toAddSubgroup).2
        Submodule.subset_span hu
    have hw : w = (m : ℚ)⁻¹ • j u := by
      rw [← h, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm), one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ hu'
  · intro w
    rw [hcl]
    constructor
    · rintro ⟨m, u, hm, h⟩
      exact ⟨m, hm, ⟨u, h.symm⟩⟩
    · rintro ⟨m, hm, u, h⟩
      exact ⟨m, u, hm, h.symm⟩
  · intro w
    constructor
    · rintro ⟨m, a, hm, ha⟩ u ⟨m', b, hm', hb⟩
      have key : ((m * m' : ℕ) : ℚ) * (s0 / 2 * formB L β w u) = (E₁ a b : ℤ) := by
        rw [hE1, ← ha, ← hb, formB_nsmul_left, formB_nsmul_right]
        push_cast
        ring
      exact Nat.Coprime.coprime_dvd_left (den_dvd_of_mul_eq_int _ _ _ key) (hm.mul_left hm')
    · intro h
      have hden : ∀ x : D'.La, (s0 / 2 * formB L β w (j x)).den.Coprime p := fun x =>
        h (j x) ⟨1, x, Nat.coprime_one_left p, one_smul _ _⟩
      let m : ℕ := ∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den
      have hm : m.Coprime p := Nat.Coprime.prod_left fun x _ => hden x
      have hint : ∀ u : D'.La, ∃ z : ℤ, (z : ℚ) = m * (s0 / 2 * formB L β w (j u)) := by
        intro u
        have hu : u ∈ Submodule.span ℤ (S : Set D'.La) := hS ▸ Submodule.mem_top
        induction hu using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun x => (s0 / 2 * formB L β w (j x)).den) hx
          refine ⟨r * (s0 / 2 * formB L β w (j x)).num, ?_⟩
          have h2 := Rat.mul_den_eq_num (s0 / 2 * formB L β w (j x))
          change (((r : ℤ) * (s0 / 2 * formB L β w (j x)).num : ℤ) : ℚ) = ((∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den : ℕ) : ℚ) * _
          rw [hr]
          push_cast
          rw [← h2]
          ring
        | zero =>
          refine ⟨0, ?_⟩
          have h0 : formB L β w (j 0) = 0 := by
            have := formB_nsmul_right L β 0 w (0 : VQ D)
            simpa using this
          rw [h0]
          simp
        | add x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          refine ⟨a + b, ?_⟩
          rw [map_add, formB_add_right]
          push_cast
          rw [ha, hb]
          ring
        | smul a x _ hx =>
          obtain ⟨b, hb⟩ := hx
          refine ⟨a * b, ?_⟩
          rw [map_zsmul, formB_zsmul_right]
          push_cast
          rw [hb]
          ring
      choose c hc using hint
      let f : D'.La →ₗ[ℤ] ℤ := AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' c (fun a b => by
        have h3 : ((c (a + b) : ℤ) : ℚ) = ((c a + c b : ℤ) : ℚ) := by
          push_cast
          rw [hc, hc, hc, map_add, formB_add_right]
          ring
        exact_mod_cast h3))
      obtain ⟨x, hx⟩ := hperf f
      obtain ⟨z, hz⟩ : ∃ z, z + j x = (e * m) • w := ⟨(e * m) • w - j x, sub_add_cancel _ _⟩
      have hs : s0 / 2 ≠ 0 := by positivity
      have hzero : ∀ u, formB L β z (j u) = 0 := by
        intro u
        have h1 : E₁ x u = e • c u := by
          have := LinearMap.congr_fun hx u
          simpa [f] using this
        have h2 : (E₁ x u : ℚ) = e * (m * (s0 / 2 * formB L β w (j u))) := by
          rw [h1, ← hc]
          push_cast
          simp
        rw [hE1] at h2
        have h3 : formB L β (z + j x) (j u) = ((e * m : ℕ) : ℚ) * formB L β w (j u) := by
          rw [hz, formB_nsmul_left]
        rw [formB_add_left] at h3
        have h4 : s0 / 2 * formB L β z (j u) = 0 := by
          have h5 : s0 / 2 * (formB L β z (j u) + formB L β (j x) (j u)) =
              s0 / 2 * (((e * m : ℕ) : ℚ) * formB L β w (j u)) := by rw [h3]
          push_cast at h5
          linarith
        exact (mul_eq_zero.1 h4).resolve_left hs
      obtain ⟨k, u₁, hk, hu₁⟩ := hspan z
      have hEF : ∀ u, D'.EF u₁ u = 0 := by
        intro u
        have h1 := hform u₁ u
        rw [← hu₁, formB_nsmul_left, hzero u] at h1
        simpa using h1
      have hu₀ : u₁ = 0 := D'.nondeg _ hEF
      have hz0 : z = 0 := by
        rw [hu₀, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at hu₁
        exact (smul_eq_zero.1 hu₁).resolve_left (by exact_mod_cast hk)
      refine ⟨e * m, x, he.mul_left hm, ?_⟩
      rw [← hz, hz0, zero_add]

end UpperTheory.Gal.W2
end
end

