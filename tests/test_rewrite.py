import unittest

from lean_compcert_probe.rewrite import mechanical_rewrite


class RewriteTests(unittest.TestCase):
    def test_rewrites_only_known_constructs(self) -> None:
        source = "LEAN_ALWAYS_INLINE __attribute__((unused)) int f(void);"
        result = mechanical_rewrite(source)
        self.assertEqual(result.text, "inline  int f(void);")
        self.assertEqual(
            result.applied,
            ("remove unused attribute", "replace force-inline macro"),
        )

    def test_unknown_source_is_unchanged(self) -> None:
        source = "uint64_t f(uint64_t x) { return x + 1; }"
        result = mechanical_rewrite(source)
        self.assertEqual(result.text, source)
        self.assertFalse(result.applied)

    def test_materializes_static_string_flexible_array(self) -> None:
        source = (
            'static const lean_string_object l_s_value = {.m_header = '
            '{.m_rc = 0}, .m_size = 3, .m_capacity = 3, .m_length = 2, '
            '.m_data = "hi"};'
        )
        result = mechanical_rewrite(source)
        self.assertIn('char m_data[sizeof("hi")];', result.text)
        self.assertIn("} l_s_value = {.m_header", result.text)
        self.assertIn("materialize static string flexible array", result.applied)

    def test_materializes_static_constructor_flexible_array(self) -> None:
        source = (
            "static const lean_ctor_object l_value = {.m_header = {.m_rc = 0}, "
            ".m_objs = {((lean_object*)&l_a),"
            "LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};"
        )
        result = mechanical_rewrite(source)
        self.assertIn("lean_object *m_objs[2];", result.text)
        self.assertIn("} l_value = {.m_header", result.text)
        self.assertIn("materialize static constructor flexible array", result.applied)

    def test_materializes_captured_static_closure(self) -> None:
        source = (
            "static const lean_closure_object l_closure = "
            "{.m_header = {.m_rc = 0}, .m_fun = (void*)l_fun, "
            ".m_arity = 3, .m_num_fixed = 2, "
            ".m_objs = {((lean_object*)&l_a),((lean_object*)&l_b)}};"
        )
        result = mechanical_rewrite(source)
        self.assertIn("lean_object *m_objs[2];", result.text)
        self.assertIn("} l_closure = {.m_header", result.text)
        self.assertIn("materialize static closure flexible array", result.applied)

    def test_materializes_zero_capture_static_closure(self) -> None:
        source = (
            "static const lean_closure_object l_closure = "
            "{.m_header = {.m_rc = 0}, .m_fun = (void*)l_fun, "
            ".m_arity = 3, .m_num_fixed = 0, .m_objs = {} };"
        )
        result = mechanical_rewrite(source)
        self.assertIn("uint16_t m_num_fixed; } l_closure", result.text)
        self.assertNotIn(".m_objs", result.text)
        self.assertIn("materialize static closure flexible array", result.applied)

    def test_materializes_static_object_array(self) -> None:
        source = (
            "static const lean_array_object l_array = "
            "{.m_header = {.m_rc = 0}, .m_size = 2, .m_capacity = 2, "
            ".m_data = {((lean_object*)&l_a),((lean_object*)&l_b)}};"
        )
        result = mechanical_rewrite(source)
        self.assertIn("lean_object * m_data[2];", result.text)
        self.assertIn("materialize static object-array flexible array", result.applied)

    def test_materializes_empty_static_object_array(self) -> None:
        source = (
            "static const lean_array_object l_array = "
            "{.m_header = {.m_rc = 0}, .m_size = 0, .m_capacity = 0, "
            ".m_data = {}};"
        )
        result = mechanical_rewrite(source)
        self.assertIn("size_t m_capacity; } l_array", result.text)
        self.assertNotIn(".m_data", result.text)
        self.assertIn("materialize static object-array flexible array", result.applied)

    def test_materializes_static_scalar_array(self) -> None:
        source = (
            "static const lean_sarray_object l_bytes = "
            "{.m_header = {.m_rc = 0}, .m_size = 3, .m_capacity = 3, "
            ".m_data = {1,2,3}};"
        )
        result = mechanical_rewrite(source)
        self.assertIn("uint8_t m_data[3];", result.text)
        self.assertIn("materialize static scalar-array flexible array", result.applied)


if __name__ == "__main__":
    unittest.main()
