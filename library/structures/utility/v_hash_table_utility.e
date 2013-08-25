note
	description: "Summary description for {V_TABLE_HASH}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	V_HASH_TABLE_UTILITY [K -> HASHABLE, V]

feature -- Basic Operations

	key_hash_code (kv: TUPLE [key: K; value: V]): INTEGER
			-- Hash code of key of `kv'.
		do
			Result := kv.key.hash_code
		end

end
