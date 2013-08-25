note
	description: "Summary description for {V_TABLE_UTILITY}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	V_TABLE_UTILITY [K, V]

feature -- Basic Operation

	keys_reference_equal (kv1, kv2: TUPLE [key: K; value: V]): BOOLEAN
			-- Are keys of `kv1' and `kv2' reference equal?
		do
			Result := kv1.key = kv2.key
		end

	keys_object_equal (kv1, kv2: TUPLE [key: K; value: V]): BOOLEAN
			-- Are keys of `kv1' and `kv2' object equal?
		do
			Result := kv1.key ~ kv2.key
		end

	keys_comparison (kv1, kv2: TUPLE [key: K; value: V]; key_eq: PREDICATE [ANY, TUPLE [K, K]]): BOOLEAN
			-- Are keys of `kv1' and `kv2' satisfying `key_eq'
		do
			Result := key_eq.item ([kv1.key, kv2.key])
		end

	key_hash_code_with (kv: TUPLE [key: K; value: V]; key_h: FUNCTION [ANY, TUPLE [K], INTEGER]): INTEGER
			-- Hash Code of the key of `kv' from `key_h'
		do
			Result := key_h.item ([kv.key])
		end

end
