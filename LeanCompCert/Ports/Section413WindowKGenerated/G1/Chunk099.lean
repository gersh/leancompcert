import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk099

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362583780195251426, 362583781427891954⟩, ⟨(-991303591821009583), (-991295329533484987)⟩, true⟩

def state01 : KState := ⟨⟨362556139834860257, 362556141070078484⟩, ⟨(-717369468779429929), (-717361180958961279)⟩, true⟩

def words00 : List Nat := [371283681038528525, 371283687787201399, 371283694396036119, 371283701003637186, 371283708352769843, 371283712024276408, 371283725909665075, 371283739792365598, 371283753463223630, 371283760767287751]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 9900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 9900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362574231819169028, 362574233057018421⟩, ⟨(-896833316841212107), (-896825002932952803)⟩, true⟩

def words01 : List Nat := [371283770193209896, 371283779617385775, 371283796039511750, 371283798903979901, 371283800415918607, 371283801927639923, 371283811578414268, 371283818195822136, 371283827310425264, 371283836423318900]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 9910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 9900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362617167880359867, 362617169120826188⟩, ⟨(-1323206820222117979), (-1323198480340186585)⟩, true⟩

def words02 : List Nat := [371283845396291453, 371283846340327104, 371283857466911611, 371283868591399960, 371283882630320525, 371283888455736087, 371283894415125820, 371283900373413904, 371283916504147015, 371283929922322494]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 9920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 9900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362511362901900678, 362511364144987917⟩, ⟨(-271578553273502172), (-271570187352625894)⟩, true⟩

def words03 : List Nat := [371283953508525069, 371283977090094761, 371283996778242831, 371284002959692281, 371284012081699900, 371284021202021784, 371284037572959212, 371284040451176920, 371284043200257292, 371284045948895711]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 9930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 9900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362556078569265230, 362556079814954861⟩, ⟨(-715871492579198141), (-715863100777120883)⟩, true⟩

def words04 : List Nat := [371284058840232659, 371284066759937748, 371284082515533579, 371284098268082950, 371284112659599423, 371284113581441081, 371284116937452319, 371284120292931768, 371284133774374261, 371284141004706935]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 9940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 9900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362577143383546861, 362577144631893582⟩, ⟨(-925446126322781848), (-925437708069242424)⟩, true⟩

def words05 : List Nat := [371284148344133990, 371284155682187680, 371284170453189079, 371284181861025375, 371284193796523813, 371284205729732472, 371284217522437886, 371284219869000153, 371284229198994090, 371284238527278660]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 9950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 9900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362539268138827601, 362539269389775016⟩, ⟨(-548024334953176230), (-548015890783155266)⟩, true⟩

def words06 : List Nat := [371284251791939493, 371284255107873158, 371284257556216582, 371284260004161729, 371284265387418481, 371284267233759111, 371284279167598266, 371284291099170241, 371284302900929254, 371284308413866566]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 9960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 9900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362601532450283138, 362601533703864019⟩, ⟨(-1169020718477236434), (-1169012248038096890)⟩, true⟩

def words07 : List Nat := [371284319245488271, 371284330075086820, 371284350979847452, 371284358490039385, 371284364229452420, 371284369967803687, 371284380688155728, 371284386469344959, 371284398207743907, 371284409943916309]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 9970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 9900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362529366485692422, 362529367741916709⟩, ⟨(-448355600666643047), (-448347103833282337)⟩, true⟩

def words08 : List Nat := [371284421841194256, 371284427783372038, 371284441443064955, 371284455100177750, 371284471681303471, 371284474905797884, 371284478006221489, 371284481106121856, 371284488151607160, 371284492643945207]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 9980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 9900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362439131937343880, 362439133196204314⟩, ⟨454109518161339849, 454118041343282001⟩, true⟩

def words09 : List Nat := [371284504728311686, 371284516810380243, 371284528775524510, 371284530650235718, 371284535461197186, 371284540271343416, 371284551564734889, 371284551565027460, 371284549541641065, 371284545000338643]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 9990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 9900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 9900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk099
