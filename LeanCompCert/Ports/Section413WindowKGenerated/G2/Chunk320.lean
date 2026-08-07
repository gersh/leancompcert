import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk320

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552125222440603, 360552131415217405⟩, ⟨958006651254006128, 958140654431876222⟩, true⟩

def state01 : KState := ⟨⟨360556725686744760, 360556731883578353⟩, ⟨810433384205091532, 810567517219919804⟩, true⟩

def words00 : List Nat := [360582072375393043, 360582070954225208, 360582068558287497, 360582067133995200, 360582065709667097, 360582063794372774, 360582061606866409, 360582058815781656, 360582056024789900, 360582054205265949]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360482770608080491, 360482776808931411⟩, ⟨3178017309766807785, 3178151571396353535⟩, true⟩

def words01 : List Nat := [360582053414566972, 360582052173279381, 360582050932026271, 360582049198172204, 360582046490371392, 360582043285237422, 360582040080177994, 360582037578080226, 360582035110479530, 360582032011036232]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360529407303629685, 360529413508503492⟩, ⟨1684320864792587324, 1684455255254686576⟩, true⟩

def words02 : List Nat := [360582028911692760, 360582025533513052, 360582022672591979, 360582020395086805, 360582018117697854, 360582014901999887, 360582011063995368, 360582008196550654, 360582005329159079, 360582003432176758]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360489099121135851, 360489105330080744⟩, ⟨2975738789111478596, 2975873309990269056⟩, true⟩

def words03 : List Nat := [360582001790715703, 360581999657918936, 360581997525161687, 360581996101064394, 360581995264172700, 360581993956546551, 360581992648955650, 360581990750482143, 360581988169566007, 360581985271091677]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360488095114919033, 360488101327882673⟩, ⟨3007876223384976829, 3008010873044528249⟩, true⟩

def words04 : List Nat := [360581982372652766, 360581980334269907, 360581977771231524, 360581974458730485, 360581971146369649, 360581967003800568, 360581963604224491, 360581960907452641, 360581958210806427, 360581955021269398]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360571264126414826, 360571270343413899⟩, ⟨341753372587537057, 341888151602882369⟩, true⟩

def words05 : List Nat := [360581952093353733, 360581950134632349, 360581948175915124, 360581945858331944, 360581943771494496, 360581940853369324, 360581937935344670, 360581935986306472, 360581934685320861, 360581934353133266]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576784213563413, 360576790434624569⟩, ⟨164604730338218506, 164739639604568306⟩, true⟩

def words06 : List Nat := [360581934020897501, 360581933203245390, 360581933150303959, 360581933608311416, 360581933608671370, 360581933381040195, 360581932182700202, 360581930236139205, 360581928289618039, 360581927311444169]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561676798643466, 360561683023728257⟩, ⟨649286169888512023, 649421208212425001⟩, true⟩

def words07 : List Nat := [360581927280325623, 360581927409451966, 360581927409832534, 360581927069114014, 360581927069471976, 360581926826096985, 360581927306342247, 360581927457213875, 360581927457595664, 360581926826976774]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603625747458191, 360603631976579630⟩, ⟨(-696694587070957871), (-696559419231338417)⟩, true⟩

def words08 : List Nat := [360581926196306686, 360581925540468645, 360581926179942335, 360581926983493928, 360581926983892258, 360581926909058239, 360581926211786062, 360581925666953284, 360581925543627969, 360581926220472581]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360605354713218169, 360605360946407940⟩, ⟨(-752276324784987554), (-752141026372539748)⟩, true⟩

def words09 : List Nat := [360581926288010346, 360581926355589817, 360581927099753965, 360581928328383961, 360581928850224834, 360581929372097809, 360581929372480377, 360581929267368471, 360581929761298116, 360581930491706450]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk320
