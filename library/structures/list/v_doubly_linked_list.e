note
	description: "[
		Doubly linked lists.
		Random access takes linear time.
		Once a position is found, inserting or removing elements to the left and right of it takes constant time
		and doesn't require reallocation of other elements.
		]"
	author: "Nadia Polikarpova"
	model: sequence

class
	V_DOUBLY_LINKED_LIST [G]

inherit
	V_LIST [G]
		redefine
			default_create,
			copy,
			first,
			last,
			put,
			prepend,
			reverse
		end

feature {NONE} -- Initialization

	default_create
			-- Create an empty list.
		do
		ensure then
			sequence_effect: sequence.is_empty
		end

feature -- Initialization

	copy (other: like Current)
			-- Initialize by copying all the items of `other'.
		note
			modify: sequence
		do
			if other /= Current then
				wipe_out
				append (other.new_cursor)
			end
		ensure then
			sequence_effect: sequence |=| other.sequence
		end

feature -- Access

	item alias "[]" (i: INTEGER): G assign put
			-- Value at position `i'.
		do
			Result := cell_at (i).item
		end

	first: G
			-- First element.
		do
			check attached first_cell as l_first then
				Result := l_first.item
			end
		end

	last: G
			-- Last element.
		do
			check attached last_cell as l_last then
				Result := l_last.item
			end
		end

feature -- Measurement

	count: INTEGER
			-- Number of elements.

feature -- Iteration

	at (i: INTEGER): V_DOUBLY_LINKED_LIST_ITERATOR [G]
			-- New iterator pointing at position `i'.
		do
			create Result.make (Current)
			if i < 1 then
				Result.go_before
			elseif i > count then
				Result.go_after
			else
				Result.go_to (i)
			end
		end

feature -- Replacement

	put (v: G; i: INTEGER)
			-- Associate `v' with index `i'.
		note
			modify: sequence
		do
			cell_at (i).put (v)
		end

	reverse
			-- Reverse the order of elements.
		note
			modify: sequence
		local
			rest, next: detachable V_DOUBLY_LINKABLE [G]
		do
			from
				last_cell := first_cell
				rest := first_cell
				first_cell := Void
			until
				rest = Void
			loop
				next := rest.right
				rest.put_right (first_cell)
				rest.put_left (next)
				first_cell := rest
				rest := next
			end
		end

feature -- Extension

	extend_front (v: G)
			-- Insert `v' at the front.
		local
			cell: V_DOUBLY_LINKABLE [G]
		do
			create cell.put (v)
			if attached first_cell as l_first then
				cell.connect (l_first)
			else
				last_cell := cell
			end
			first_cell := cell
			count := count + 1
		end

	extend_back (v: G)
			-- Insert `v' at the back.
		local
			cell: V_DOUBLY_LINKABLE [G]
		do
			create cell.put (v)
			if attached last_cell as l_last then
				l_last.connect (cell)
			else
				first_cell := cell
			end
			last_cell := cell
			count := count + 1
		end

	extend_at (v: G; i: INTEGER)
			-- Insert `v' at position `i'.
		do
			if i = 1 then
				extend_front (v)
			elseif i = count + 1 then
				extend_back (v)
			else
				extend_after (v, cell_at (i - 1))
			end
		end

	prepend (input: V_ITERATOR [G])
			-- Prepend sequence of values, over which `input' iterates.
		local
			it: V_DOUBLY_LINKED_LIST_ITERATOR [G]
		do
			if not input.after then
				extend_front (input.item)
				input.forth
				from
					it := new_cursor
				until
					input.after
				loop
					it.extend_right (input.item)
					it.forth
					input.forth
				end
			end
		end

	insert_at (input: V_ITERATOR [G]; i: INTEGER)
			-- Insert sequence of values, over which `input' iterates, starting at position `i'.
		local
			it: V_DOUBLY_LINKED_LIST_ITERATOR [G]
		do
			if i = 1 then
				prepend (input)
			else
				from
					it := at (i - 1)
				until
					input.after
				loop
					it.extend_right (input.item)
					it.forth
					input.forth
				end
			end
		end

feature -- Removal

	remove_front
			-- Remove first element.
		do
			check attached first_cell as l_first then
				if attached l_first.right as l_first_right then
					l_first_right.put_left (Void)
				else
					check count = 1 end
					last_cell := Void
				end
				first_cell := l_first.right
			end
			count := count - 1
		end

	remove_back
			-- Remove last element.
		do
			check attached last_cell as l_last then
				if attached l_last.left as l_last_left then
					l_last_left.put_right (Void)
				else
					check count = 1 end
					first_cell := Void
				end
				last_cell := l_last.left
			end
			count := count - 1
		end

	remove_at  (i: INTEGER)
			-- Remove element at position `i'.
		do
			if i = 1 then
				remove_front
			else
				remove_after (cell_at (i - 1))
			end
		end

	wipe_out
			-- Remove all elements.
		do
			first_cell := Void
			last_cell := Void
			count := 0
		end

feature {V_CONTAINER, V_ITERATOR} -- Implementation

	first_cell: detachable V_DOUBLY_LINKABLE [G]
			-- First cell of the list.

	last_cell: detachable V_DOUBLY_LINKABLE [G]
			-- Last cell of the list.

	cell_at (i: INTEGER): V_DOUBLY_LINKABLE [G]
			-- Cell at position `i'.
		require
			valid_position: 1 <= i and i <= count
		local
			j: INTEGER
		do
			if i <= count // 2 then
				from
					j := 1
					check attached first_cell as l_first then
						Result := l_first
					end
				until
					j = i
				loop
					check attached  Result.right as l_right then
						Result := l_right
					end
					j := j + 1
				end
			else
				from
					j := count
					check attached last_cell as l_last then
						Result := l_last
					end
				until
					j = i
				loop
					check attached Result.left as l_left then
						Result := l_left
					end
					j := j - 1
				end
			end
		end

	extend_after (v: G; c: V_DOUBLY_LINKABLE [G])
			-- Add a new cell with value `v' after `c'.
		require
			c_exists: c /= Void
		local
			new: V_DOUBLY_LINKABLE [G]
		do
			create new.put (v)
			if attached c.right as c_right then
				new.connect (c_right)
			else
				last_cell := new
			end
			c.connect (new)
			count := count + 1
		end

	remove_after (c: V_DOUBLY_LINKABLE [G])
			-- Remove the cell to the right of `c'.
		require
			c_exists: c /= Void
			c_right_exists: c.right /= Void
		do
			check attached c.right as l_c_right then
				c.put_right (l_c_right.right)
			end
			if attached c.right as l_c_right then
				l_c_right.put_left (c)
			else
				last_cell := c
			end
			count := count - 1
		end

	merge_after (other: V_DOUBLY_LINKED_LIST [G]; c: detachable V_DOUBLY_LINKABLE [G])
			-- Merge `other' into `Current' after cell `c'. If `c' is `Void', merge to the front.
		require
			other_exists: other /= Void
		do
			if not other.is_empty then
				check attached other.first_cell as other_first and attached other.last_cell as other_last then
					count := count + other.count
					other.wipe_out
					if c = Void then
						if attached first_cell as l_first then
							other_last.connect (l_first)
						else
							last_cell := other_last
						end
						first_cell := other_first
					else
						if attached c.right as c_right then
							other_last.connect (c_right)
						else
							last_cell := other_last
						end
						c.connect (other_first)
					end
				end
			end
		end

feature -- Specification

	sequence: MML_SEQUENCE [G]
			-- Sequence of elements.
		note
			status: specification
		local
			c: detachable V_DOUBLY_LINKABLE [G]
		do
			create Result
			from
				c := first_cell
			until
				c = Void
			loop
				Result := Result & c.item
				c := c.right
			end
		end

invariant
	first_cell_exists_in_nonempty: is_empty = (first_cell = Void)
	last_cell_exists_in_nonempty: is_empty = (last_cell = Void)
	count_definition: count = sequence.count
end
