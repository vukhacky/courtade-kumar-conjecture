module
public import CK.Certificate.ClockPilotLogs

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace CK.Certificate.CubicEndpointLogs
noncomputable section

theorem log00 : (31465551632885741/10000000000000000:ℝ) ≤ Real.log (1000/43:ℝ) ∧ Real.log (1000/43:ℝ) ≤ (15732775816442883/5000000000000000:ℝ) := by
  have hr : (3739664410487933/10000000000000000:ℝ) ≤ Real.log (125/86:ℝ) ∧ Real.log (125/86:ℝ) ≤ (1869832205243967/5000000000000000:ℝ) := by
    convert logCertificate_sound (q:=125/86) (lower:=3739664410487933/10000000000000000) (upper:=1869832205243967/5000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (1000/43:ℝ) = 4*Real.log 2+Real.log (125/86:ℝ) := by
    rw [show (1000/43:ℝ)=2^4*(125/86) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log01 : (439518875291827/10000000000000000:ℝ) ≤ Real.log (1000/957:ℝ) ∧ Real.log (1000/957:ℝ) ≤ (109879718822957/2500000000000000:ℝ) := by
  have hr : (439518875291827/10000000000000000:ℝ) ≤ Real.log (1000/957:ℝ) ∧ Real.log (1000/957:ℝ) ≤ (109879718822957/2500000000000000:ℝ) := by
    convert logCertificate_sound (q:=1000/957) (lower:=439518875291827/10000000000000000) (upper:=109879718822957/2500000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (1000/957:ℝ) = 0*Real.log 2+Real.log (1000/957:ℝ) := by
    rw [show (1000/957:ℝ)=2^0*(1000/957) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log02 : (8237732971138549/5000000000000000:ℝ) ≤ Real.log (2000000000000/385043326883:ℝ) ∧ Real.log (2000000000000/385043326883:ℝ) ≤ (16475465942277111/10000000000000000:ℝ) := by
  have hr : (1306261165539097/5000000000000000:ℝ) ≤ Real.log (500000000000/385043326883:ℝ) ∧ Real.log (500000000000/385043326883:ℝ) ≤ (522504466215639/2000000000000000:ℝ) := by
    convert logCertificate_sound (q:=500000000000/385043326883) (lower:=1306261165539097/5000000000000000) (upper:=522504466215639/2000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (2000000000000/385043326883:ℝ) = 2*Real.log 2+Real.log (500000000000/385043326883:ℝ) := by
    rw [show (2000000000000/385043326883:ℝ)=2^2*(500000000000/385043326883) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log03 : (2138390520365283/10000000000000000:ℝ) ≤ Real.log (2000000000000/1614956673117:ℝ) ∧ Real.log (2000000000000/1614956673117:ℝ) ≤ (534597630091321/2500000000000000:ℝ) := by
  have hr : (2138390520365283/10000000000000000:ℝ) ≤ Real.log (2000000000000/1614956673117:ℝ) ∧ Real.log (2000000000000/1614956673117:ℝ) ≤ (534597630091321/2500000000000000:ℝ) := by
    convert logCertificate_sound (q:=2000000000000/1614956673117) (lower:=2138390520365283/10000000000000000) (upper:=534597630091321/2500000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (2000000000000/1614956673117:ℝ) = 0*Real.log 2+Real.log (2000000000000/1614956673117:ℝ) := by
    rw [show (2000000000000/1614956673117:ℝ)=2^0*(2000000000000/1614956673117) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log04 : (36888794541139357/10000000000000000:ℝ) ≤ Real.log (40:ℝ) ∧ Real.log (40:ℝ) ≤ (9222198635284847/2500000000000000:ℝ) := by
  have hr : (2231435513142097/10000000000000000:ℝ) ≤ Real.log (5/4:ℝ) ∧ Real.log (5/4:ℝ) ≤ (1115717756571049/5000000000000000:ℝ) := by
    convert logCertificate_sound (q:=5/4) (lower:=2231435513142097/10000000000000000) (upper:=1115717756571049/5000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (40:ℝ) = 5*Real.log 2+Real.log (5/4:ℝ) := by
    rw [show (40:ℝ)=2^5*(5/4) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log05 : (126589039921449/5000000000000000:ℝ) ≤ Real.log (40/39:ℝ) ∧ Real.log (40/39:ℝ) ≤ (253178079842899/10000000000000000:ℝ) := by
  have hr : (126589039921449/5000000000000000:ℝ) ≤ Real.log (40/39:ℝ) ∧ Real.log (40/39:ℝ) ≤ (253178079842899/10000000000000000:ℝ) := by
    convert logCertificate_sound (q:=40/39) (lower:=126589039921449/5000000000000000) (upper:=253178079842899/10000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (40/39:ℝ) = 0*Real.log 2+Real.log (40/39:ℝ) := by
    rw [show (40/39:ℝ)=2^0*(40/39) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log06 : (18111202043791513/10000000000000000:ℝ) ≤ Real.log (200000000000/32694182673:ℝ) ∧ Real.log (200000000000/32694182673:ℝ) ≤ (9055601021895763/5000000000000000:ℝ) := by
  have hr : (4248258432592609/10000000000000000:ℝ) ≤ Real.log (50000000000/32694182673:ℝ) ∧ Real.log (50000000000/32694182673:ℝ) ≤ (424825843259261/1000000000000000:ℝ) := by
    convert logCertificate_sound (q:=50000000000/32694182673) (lower:=4248258432592609/10000000000000000) (upper:=424825843259261/1000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (200000000000/32694182673:ℝ) = 2*Real.log 2+Real.log (50000000000/32694182673:ℝ) := by
    rw [show (200000000000/32694182673:ℝ)=2^2*(50000000000/32694182673) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log07 : (446234968326837/2500000000000000:ℝ) ≤ Real.log (200000000000/167305817327:ℝ) ∧ Real.log (200000000000/167305817327:ℝ) ≤ (1784939873307349/10000000000000000:ℝ) := by
  have hr : (446234968326837/2500000000000000:ℝ) ≤ Real.log (200000000000/167305817327:ℝ) ∧ Real.log (200000000000/167305817327:ℝ) ≤ (1784939873307349/10000000000000000:ℝ) := by
    convert logCertificate_sound (q:=200000000000/167305817327) (lower:=446234968326837/2500000000000000) (upper:=1784939873307349/10000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (200000000000/167305817327:ℝ) = 0*Real.log 2+Real.log (200000000000/167305817327:ℝ) := by
    rw [show (200000000000/167305817327:ℝ)=2^0*(200000000000/167305817327) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log08 : (8800221514456137/5000000000000000:ℝ) ≤ Real.log (1000000000000/172037241907:ℝ) ∧ Real.log (1000000000000/172037241907:ℝ) ≤ (17600443028912287/10000000000000000:ℝ) := by
  have hr : (373749941771337/1000000000000000:ℝ) ≤ Real.log (250000000000/172037241907:ℝ) ∧ Real.log (250000000000/172037241907:ℝ) ≤ (3737499417713371/10000000000000000:ℝ) := by
    convert logCertificate_sound (q:=250000000000/172037241907) (lower:=373749941771337/1000000000000000) (upper:=3737499417713371/10000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (1000000000000/172037241907:ℝ) = 2*Real.log 2+Real.log (250000000000/172037241907:ℝ) := by
    rw [show (1000000000000/172037241907:ℝ)=2^2*(250000000000/172037241907) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log09 : (1887871037569753/10000000000000000:ℝ) ≤ Real.log (1000000000000/827962758093:ℝ) ∧ Real.log (1000000000000/827962758093:ℝ) ≤ (943935518784877/5000000000000000:ℝ) := by
  have hr : (1887871037569753/10000000000000000:ℝ) ≤ Real.log (1000000000000/827962758093:ℝ) ∧ Real.log (1000000000000/827962758093:ℝ) ≤ (943935518784877/5000000000000000:ℝ) := by
    convert logCertificate_sound (q:=1000000000000/827962758093) (lower:=1887871037569753/10000000000000000) (upper:=943935518784877/5000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (1000000000000/827962758093:ℝ) = 0*Real.log 2+Real.log (1000000000000/827962758093:ℝ) := by
    rw [show (1000000000000/827962758093:ℝ)=2^0*(1000000000000/827962758093) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log10 : (41997050778799263/10000000000000000:ℝ) ≤ Real.log (200/3:ℝ) ∧ Real.log (200/3:ℝ) ≤ (419970507787993/100000000000000:ℝ) := by
  have hr : (408219945202551/10000000000000000:ℝ) ≤ Real.log (25/24:ℝ) ∧ Real.log (25/24:ℝ) ≤ (51027493150319/1250000000000000:ℝ) := by
    convert logCertificate_sound (q:=25/24) (lower:=408219945202551/10000000000000000) (upper:=51027493150319/1250000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (200/3:ℝ) = 6*Real.log 2+Real.log (25/24:ℝ) := by
    rw [show (200/3:ℝ)=2^6*(25/24) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log11 : (151136378100481/10000000000000000:ℝ) ≤ Real.log (200/197:ℝ) ∧ Real.log (200/197:ℝ) ≤ (75568189050241/5000000000000000:ℝ) := by
  have hr : (151136378100481/10000000000000000:ℝ) ≤ Real.log (200/197:ℝ) ∧ Real.log (200/197:ℝ) ≤ (75568189050241/5000000000000000:ℝ) := by
    convert logCertificate_sound (q:=200/197) (lower:=151136378100481/10000000000000000) (upper:=75568189050241/5000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (200/197:ℝ) = 0*Real.log 2+Real.log (200/197:ℝ) := by
    rw [show (200/197:ℝ)=2^0*(200/197) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log12 : (18871376384594083/10000000000000000:ℝ) ≤ Real.log (1000000000000/151504850437:ℝ) ∧ Real.log (1000000000000/151504850437:ℝ) ≤ (1179461024037131/625000000000000:ℝ) := by
  have hr : (5008432773395179/10000000000000000:ℝ) ≤ Real.log (250000000000/151504850437:ℝ) ∧ Real.log (250000000000/151504850437:ℝ) ≤ (250421638669759/500000000000000:ℝ) := by
    convert logCertificate_sound (q:=250000000000/151504850437) (lower:=5008432773395179/10000000000000000) (upper:=250421638669759/500000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (1000000000000/151504850437:ℝ) = 2*Real.log 2+Real.log (250000000000/151504850437:ℝ) := by
    rw [show (1000000000000/151504850437:ℝ)=2^2*(250000000000/151504850437) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log13 : (821454554042897/5000000000000000:ℝ) ≤ Real.log (1000000000000/848495149563:ℝ) ∧ Real.log (1000000000000/848495149563:ℝ) ≤ (328581821617159/2000000000000000:ℝ) := by
  have hr : (821454554042897/5000000000000000:ℝ) ≤ Real.log (1000000000000/848495149563:ℝ) ∧ Real.log (1000000000000/848495149563:ℝ) ≤ (328581821617159/2000000000000000:ℝ) := by
    convert logCertificate_sound (q:=1000000000000/848495149563) (lower:=821454554042897/5000000000000000) (upper:=328581821617159/2000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (1000000000000/848495149563:ℝ) = 0*Real.log 2+Real.log (1000000000000/848495149563:ℝ) := by
    rw [show (1000000000000/848495149563:ℝ)=2^0*(1000000000000/848495149563) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log14 : (467692498245623/250000000000000:ℝ) ≤ Real.log (2000000000000/308010066709:ℝ) ∧ Real.log (2000000000000/308010066709:ℝ) ≤ (18707699929824933/10000000000000000:ℝ) := by
  have hr : (151398634957063/312500000000000:ℝ) ≤ Real.log (500000000000/308010066709:ℝ) ∧ Real.log (500000000000/308010066709:ℝ) ≤ (4844756318626017/10000000000000000:ℝ) := by
    convert logCertificate_sound (q:=500000000000/308010066709) (lower:=151398634957063/312500000000000) (upper:=4844756318626017/10000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (2000000000000/308010066709:ℝ) = 2*Real.log 2+Real.log (500000000000/308010066709:ℝ) := by
    rw [show (2000000000000/308010066709:ℝ)=2^2*(500000000000/308010066709) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log15 : (836209344926101/5000000000000000:ℝ) ≤ Real.log (2000000000000/1691989933291:ℝ) ∧ Real.log (2000000000000/1691989933291:ℝ) ≤ (1672418689852203/10000000000000000:ℝ) := by
  have hr : (836209344926101/5000000000000000:ℝ) ≤ Real.log (2000000000000/1691989933291:ℝ) ∧ Real.log (2000000000000/1691989933291:ℝ) ≤ (1672418689852203/10000000000000000:ℝ) := by
    convert logCertificate_sound (q:=2000000000000/1691989933291) (lower:=836209344926101/5000000000000000) (upper:=1672418689852203/10000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (2000000000000/1691989933291:ℝ) = 0*Real.log 2+Real.log (2000000000000/1691989933291:ℝ) := by
    rw [show (2000000000000/1691989933291:ℝ)=2^0*(2000000000000/1691989933291) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log16 : (10857014803801499/2500000000000000:ℝ) ≤ Real.log (1000/13:ℝ) ∧ Real.log (1000/13:ℝ) ≤ (43428059215206033/10000000000000000:ℝ) := by
  have hr : (459807095402321/2500000000000000:ℝ) ≤ Real.log (125/104:ℝ) ∧ Real.log (125/104:ℝ) ≤ (367845676321857/2000000000000000:ℝ) := by
    convert logCertificate_sound (q:=125/104) (lower:=459807095402321/2500000000000000) (upper:=367845676321857/2000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (1000/13:ℝ) = 6*Real.log 2+Real.log (125/104:ℝ) := by
    rw [show (1000/13:ℝ)=2^6*(125/104) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log17 : (65426197743277/5000000000000000:ℝ) ≤ Real.log (1000/987:ℝ) ∧ Real.log (1000/987:ℝ) ≤ (26170479097311/2000000000000000:ℝ) := by
  have hr : (65426197743277/5000000000000000:ℝ) ≤ Real.log (1000/987:ℝ) ∧ Real.log (1000/987:ℝ) ≤ (26170479097311/2000000000000000:ℝ) := by
    convert logCertificate_sound (q:=1000/987) (lower:=65426197743277/5000000000000000) (upper:=26170479097311/2000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (1000/987:ℝ) = 0*Real.log 2+Real.log (1000/987:ℝ) := by
    rw [show (1000/987:ℝ)=2^0*(1000/987) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log18 : (3806046696810207/2000000000000000:ℝ) ≤ Real.log (15625000000/2329954751:ℝ) ∧ Real.log (15625000000/2329954751:ℝ) ≤ (2378779185506381/1250000000000000:ℝ) := by
  have hr : (5167289872852131/10000000000000000:ℝ) ≤ Real.log (3906250000/2329954751:ℝ) ∧ Real.log (3906250000/2329954751:ℝ) ≤ (1291822468213033/2500000000000000:ℝ) := by
    convert logCertificate_sound (q:=3906250000/2329954751) (lower:=5167289872852131/10000000000000000) (upper:=1291822468213033/2500000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (15625000000/2329954751:ℝ) = 2*Real.log 2+Real.log (3906250000/2329954751:ℝ) := by
    rw [show (15625000000/2329954751:ℝ)=2^2*(3906250000/2329954751) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log19 : (100925479670829/625000000000000:ℝ) ≤ Real.log (15625000000/13295045249:ℝ) ∧ Real.log (15625000000/13295045249:ℝ) ≤ (322961534946653/2000000000000000:ℝ) := by
  have hr : (100925479670829/625000000000000:ℝ) ≤ Real.log (15625000000/13295045249:ℝ) ∧ Real.log (15625000000/13295045249:ℝ) ≤ (322961534946653/2000000000000000:ℝ) := by
    convert logCertificate_sound (q:=15625000000/13295045249) (lower:=100925479670829/625000000000000) (upper:=322961534946653/2000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (15625000000/13295045249:ℝ) = 0*Real.log 2+Real.log (15625000000/13295045249:ℝ) := by
    rw [show (15625000000/13295045249:ℝ)=2^0*(15625000000/13295045249) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log20 : (9492068925355857/5000000000000000:ℝ) ≤ Real.log (500000000000/74903027731:ℝ) ∧ Real.log (500000000000/74903027731:ℝ) ≤ (18984137850711727/10000000000000000:ℝ) := by
  have hr : (512119423951281/1000000000000000:ℝ) ≤ Real.log (125000000000/74903027731:ℝ) ∧ Real.log (125000000000/74903027731:ℝ) ≤ (5121194239512811/10000000000000000:ℝ) := by
    convert logCertificate_sound (q:=125000000000/74903027731) (lower:=512119423951281/1000000000000000) (upper:=5121194239512811/10000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (500000000000/74903027731:ℝ) = 2*Real.log 2+Real.log (125000000000/74903027731:ℝ) := by
    rw [show (500000000000/74903027731:ℝ)=2^2*(125000000000/74903027731) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log21 : (1622907854798947/10000000000000000:ℝ) ≤ Real.log (500000000000/425096972269:ℝ) ∧ Real.log (500000000000/425096972269:ℝ) ≤ (405726963699737/2500000000000000:ℝ) := by
  have hr : (1622907854798947/10000000000000000:ℝ) ≤ Real.log (500000000000/425096972269:ℝ) ∧ Real.log (500000000000/425096972269:ℝ) ≤ (405726963699737/2500000000000000:ℝ) := by
    convert logCertificate_sound (q:=500000000000/425096972269) (lower:=1622907854798947/10000000000000000) (upper:=405726963699737/2500000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (500000000000/425096972269:ℝ) = 0*Real.log 2+Real.log (500000000000/425096972269:ℝ) := by
    rw [show (500000000000/425096972269:ℝ)=2^0*(500000000000/425096972269) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log22 : (43820266346738809/10000000000000000:ℝ) ≤ Real.log (80:ℝ) ∧ Real.log (80:ℝ) ≤ (21910133173369423/5000000000000000:ℝ) := by
  have hr : (2231435513142097/10000000000000000:ℝ) ≤ Real.log (5/4:ℝ) ∧ Real.log (5/4:ℝ) ≤ (1115717756571049/5000000000000000:ℝ) := by
    convert logCertificate_sound (q:=5/4) (lower:=2231435513142097/10000000000000000) (upper:=1115717756571049/5000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (80:ℝ) = 6*Real.log 2+Real.log (5/4:ℝ) := by
    rw [show (80:ℝ)=2^6*(5/4) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log23 : (125787822068601/10000000000000000:ℝ) ≤ Real.log (80/79:ℝ) ∧ Real.log (80/79:ℝ) ≤ (62893911034301/5000000000000000:ℝ) := by
  have hr : (125787822068601/10000000000000000:ℝ) ≤ Real.log (80/79:ℝ) ∧ Real.log (80/79:ℝ) ≤ (62893911034301/5000000000000000:ℝ) := by
    convert logCertificate_sound (q:=80/79) (lower:=125787822068601/10000000000000000) (upper:=62893911034301/5000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (80/79:ℝ) = 0*Real.log 2+Real.log (80/79:ℝ) := by
    rw [show (80/79:ℝ)=2^0*(80/79) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log24 : (595947491593043/312500000000000:ℝ) ≤ Real.log (500000000000/74260273023:ℝ) ∧ Real.log (500000000000/74260273023:ℝ) ≤ (19070319730977389/10000000000000000:ℝ) := by
  have hr : (650922014972309/1250000000000000:ℝ) ≤ Real.log (125000000000/74260273023:ℝ) ∧ Real.log (125000000000/74260273023:ℝ) ≤ (5207376119778473/10000000000000000:ℝ) := by
    convert logCertificate_sound (q:=125000000000/74260273023) (lower:=650922014972309/1250000000000000) (upper:=5207376119778473/10000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (500000000000/74260273023:ℝ) = 2*Real.log 2+Real.log (125000000000/74260273023:ℝ) := by
    rw [show (500000000000/74260273023:ℝ)=2^2*(125000000000/74260273023) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log25 : (401949771020811/2500000000000000:ℝ) ≤ Real.log (500000000000/425739726977:ℝ) ∧ Real.log (500000000000/425739726977:ℝ) ≤ (321559816816649/2000000000000000:ℝ) := by
  have hr : (401949771020811/2500000000000000:ℝ) ≤ Real.log (500000000000/425739726977:ℝ) ∧ Real.log (500000000000/425739726977:ℝ) ≤ (321559816816649/2000000000000000:ℝ) := by
    convert logCertificate_sound (q:=500000000000/425739726977) (lower:=401949771020811/2500000000000000) (upper:=321559816816649/2000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (500000000000/425739726977:ℝ) = 0*Real.log 2+Real.log (500000000000/425739726977:ℝ) := by
    rw [show (500000000000/425739726977:ℝ)=2^0*(500000000000/425739726977) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log26 : (3760300476813797/2000000000000000:ℝ) ≤ Real.log (2000000000000/305134365169:ℝ) ∧ Real.log (2000000000000/305134365169:ℝ) ≤ (9400751192034499/5000000000000000:ℝ) := by
  have hr : (4938558772870081/10000000000000000:ℝ) ≤ Real.log (500000000000/305134365169:ℝ) ∧ Real.log (500000000000/305134365169:ℝ) ≤ (2469279386435041/5000000000000000:ℝ) := by
    convert logCertificate_sound (q:=500000000000/305134365169) (lower:=4938558772870081/10000000000000000) (upper:=2469279386435041/5000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (2000000000000/305134365169:ℝ) = 2*Real.log 2+Real.log (500000000000/305134365169:ℝ) := by
    rw [show (2000000000000/305134365169:ℝ)=2^2*(500000000000/305134365169) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log27 : (1655437143558177/10000000000000000:ℝ) ≤ Real.log (2000000000000/1694865634831:ℝ) ∧ Real.log (2000000000000/1694865634831:ℝ) ≤ (827718571779089/5000000000000000:ℝ) := by
  have hr : (1655437143558177/10000000000000000:ℝ) ≤ Real.log (2000000000000/1694865634831:ℝ) ∧ Real.log (2000000000000/1694865634831:ℝ) ≤ (827718571779089/5000000000000000:ℝ) := by
    convert logCertificate_sound (q:=2000000000000/1694865634831) (lower:=1655437143558177/10000000000000000) (upper:=827718571779089/5000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (2000000000000/1694865634831:ℝ) = 0*Real.log 2+Real.log (2000000000000/1694865634831:ℝ) := by
    rw [show (2000000000000/1694865634831:ℝ)=2^0*(2000000000000/1694865634831) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log28 : (46051701859880907/10000000000000000:ℝ) ≤ Real.log (100:ℝ) ∧ Real.log (100:ℝ) ≤ (2878231366242559/625000000000000:ℝ) := by
  have hr : (892574205256839/2000000000000000:ℝ) ≤ Real.log (25/16:ℝ) ∧ Real.log (25/16:ℝ) ≤ (1115717756571049/2500000000000000:ℝ) := by
    convert logCertificate_sound (q:=25/16) (lower:=892574205256839/2000000000000000) (upper:=1115717756571049/2500000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (100:ℝ) = 6*Real.log 2+Real.log (25/16:ℝ) := by
    rw [show (100:ℝ)=2^6*(25/16) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log29 : (50251679267507/5000000000000000:ℝ) ≤ Real.log (100/99:ℝ) ∧ Real.log (100/99:ℝ) ≤ (20100671707003/2000000000000000:ℝ) := by
  have hr : (50251679267507/5000000000000000:ℝ) ≤ Real.log (100/99:ℝ) ∧ Real.log (100/99:ℝ) ≤ (20100671707003/2000000000000000:ℝ) := by
    convert logCertificate_sound (q:=100/99) (lower:=50251679267507/5000000000000000) (upper:=20100671707003/2000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (100/99:ℝ) = 0*Real.log 2+Real.log (100/99:ℝ) := by
    rw [show (100/99:ℝ)=2^0*(100/99) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log30 : (1927299161991691/1000000000000000:ℝ) ≤ Real.log (2000000000000/291081500251:ℝ) ∧ Real.log (2000000000000/291081500251:ℝ) ≤ (19272991619916923/10000000000000000:ℝ) := by
  have hr : (2705024004359003/5000000000000000:ℝ) ≤ Real.log (500000000000/291081500251:ℝ) ∧ Real.log (500000000000/291081500251:ℝ) ≤ (5410048008718007/10000000000000000:ℝ) := by
    convert logCertificate_sound (q:=500000000000/291081500251) (lower:=2705024004359003/5000000000000000) (upper:=5410048008718007/10000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (2000000000000/291081500251:ℝ) = 2*Real.log 2+Real.log (500000000000/291081500251:ℝ) := by
    rw [show (2000000000000/291081500251:ℝ)=2^2*(500000000000/291081500251) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

theorem log31 : (786432332086783/5000000000000000:ℝ) ≤ Real.log (2000000000000/1708918499749:ℝ) ∧ Real.log (2000000000000/1708918499749:ℝ) ≤ (1572864664173567/10000000000000000:ℝ) := by
  have hr : (786432332086783/5000000000000000:ℝ) ≤ Real.log (2000000000000/1708918499749:ℝ) ∧ Real.log (2000000000000/1708918499749:ℝ) ≤ (1572864664173567/10000000000000000:ℝ) := by
    convert logCertificate_sound (q:=2000000000000/1708918499749) (lower:=786432332086783/5000000000000000) (upper:=1572864664173567/10000000000000000) (n:=16)
      (by unfold logCertificate; decide +kernel) using 1 <;> norm_num
  have he : Real.log (2000000000000/1708918499749:ℝ) = 0*Real.log 2+Real.log (2000000000000/1708918499749:ℝ) := by
    rw [show (2000000000000/1708918499749:ℝ)=2^0*(2000000000000/1708918499749) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [hr.1,hr.2,P03.log_two_bounds.1,P03.log_two_bounds.2]

end
end CK.Certificate.CubicEndpointLogs
