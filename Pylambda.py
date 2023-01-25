#!/usr/bin/env python
# -*- coding: utf-8 -*-

import os
import time

'''
Term structure:
[0, str:name, None] = Variable
[1, term:param, term:body] = Abstraction
[2, term:left, term:right] = Application
[3, str:name, None] = Named Term. These are used to abstract and optimize
the code: Until it is required to preform a beta-reduction will act as 
a variable.
'''

# Only one instance of this class should be used per program, otherwise
#   named term conflicts may arise.
class Pylambda:
	def __init__(self):
		self.named_terms = {}
		# Used for parsing terms. Contains list of characters.
		self._atoms = []
		# Used for unpacking named terms.
		self._nam_name = ''
	
	# Terms are saved as a string rep, and parsed only when needed.
	# Currently there's a bug, where if the first reduction in a named term
	#    is of another named term, the program stops.
	#    If this is the case the function pre-preforms the reduction.
	def define(self, name, raw):
		term = self.parse(raw)
		new_term, response = self.beta(term)
		if response == 2:
			self.named_terms[str(name)] = self.str(new_term)
		else:
			self.named_terms[str(name)] = raw.replace('@','λ').replace('\\','λ')
	
	# parse only does string preprocessing. Actual building of term is
	#   done recursively with the following 3 functions:
	'''
	_parse_app: absorbs terms as long as it can, stacking them together.
	  If it only gets one term it returns it. Applications stack from the 
	  left, so this is done with a loop.
	_parse_abs: also stacks terms together. Because abstractions 
	  stack from the right, this is done recursively.
	_parse_term: decides whether a term is an app, abs, or a var/named term.
	'''
	def parse(self, string):
		if string.count('(') != string.count(')'):
			return [0, 'Error: unmatched parenthesis']
		
		string = string.replace('@','λ').replace('\\','λ')
		for char in ('λ.()'):
			string = string.replace(char, f' {char} ')

		self._atoms = string.split()
		try:
			term = self._parse_app()
		except RecursionError:
			# Unbounded recursion only happens in ._parse_abs, so this error
			#    will only be caused by it.
			return [0, 'Error: Improper Abstraction']
		return term
	
	# Advances through the character stack, makes sure it is never empty.
	def _advance(self):
		first = self._atoms.pop(0)
		self._atoms += [None] * int(not bool(self._atoms))
		return first
	
	def _parse_term(self):
		if (first := self._atoms[0]) == '(':  # May be either app or nested abs.
			self._advance()
			if self._atoms[0] == 'λ':  # Checks if nested abs.
				self._advance()
				return self._parse_abs()
			return self._parse_app()
		elif first == 'λ':  # Only triggers for top-level abs.
			self._advance()
			return self._parse_abs()
		
		# Creates var or nam.
		name = self._advance()
		if str(name) not in self.named_terms:
			return [0, str(name)]
		return [3, str(name)]
	
	def _parse_app(self):
		left = self._parse_term()
		while self._atoms[0] not in [')', None]:
			left = [2, left, self._parse_term()]
		self._advance()
		return left
	
	def _parse_abs(self):
		param = self._parse_term()
		if self._atoms[0] != '.':
			return [1, param, self._parse_abs()]
		self._advance()
		
		body = self.alpha(self._parse_app(), param, param)
		return [1, param, body]
	
	# Returns a var with a new name. 
	def _new_name(self, term):
		if term[0] != 0:
			return None
		
		return [0, term[1] + "'"]
		
		#n, *i = term[1].split('_') + [0]
		#i = str(i[0]) 
		#return [0, f'{n}_{i}']
	
	# Creates string representation of term.
	def str(self, term):
		if term[0] in [0, 3]:  # Is var or nam.
			return str(term[1])
		elif term[0] == 1:  # Is abs.
			param = self.str(term[1])
			body = self.str(term[2])
			return f'λ{param}.{body}'.replace('.λ',' ')
		elif term[0] == 2:  # Is app.
			lb = term[1][0] == 1
			rb = term[2][0] in [1, 2]
			cb = not rb and not lb
			
			left = f'{"("*lb}{self.str(term[1])}{")"*lb}'
			right = f'{"("*rb}{self.str(term[2])}{")"*rb}'
			return f'{left}{" "*cb}{right}'
	
	# Returns set of names of vars, not the actual vars.
	def vars(self, term):
		if term[0] == 0:
			return set(term[1])
		elif term[0] == 1:
			return set(term[1][1]) | self.vars(term[2])
		elif term[0] == 2:
			return self.vars(term[1]) | self.vars(term[2])
		# If is nam, doesn't have any visible vars.
		return set()
	
	# Exchanges all instances of old var with new term. Creates deep 
	#   copy of the entered term.
	def alpha(self, term, old_var, new_term):
		if term[0] == 0:
			if term[1] == old_var[1]:
				return new_term
			return [0, term[1]]
		
		elif term[0] == 1:  # Is abs
			# If the abs's parameter is in the new term, direct
			#   replacement may cause variable conflict.
			#   A new name is found and the var inside the new term 
			#   is renamed.
			unavailiable = self.vars(new_term)
			param = term[1]
			while param[1] in unavailiable:
				param = self._new_name(param)

			if term[1] != param:  # Renaming only happens if necesary.
				new_term = self.alpha(new_term, term[1], param)
			
			# Counterintuitively propagates to parameter. Comes into play
			#   when preventing variable conflict as described above.
			param = self.alpha(term[1], old_var, new_term)
			body = self.alpha(term[2], old_var, new_term)
			return [1, param, body]
		
		elif term[0] == 2:
			left = self.alpha(term[1], old_var, new_term)
			right = self.alpha(term[2], old_var, new_term)
			return [2, left, right]
		
		elif term[0] == 3:
			# nam instances do not change, doesn't have to be deep copied.
			return term
	
	# Internal representation of beta-reduction. Limit = 1 means nams 
	#   may not be reduced yet. modifies the inputed term directly.
	#   returns the modified term as well as a "response code". 0 means
	#   no reduction has been done, 1 means a beta-reduction, 2 means
	#   named term has been unpacked.
	def _reduce(self, term, limit):
		if term[0] == 0:
			return term, 0

		# Does not actually preform beta reduction. Abs needs input,
		#   which needs to be provided by an app.
		elif term[0] == 1:
			term[2], response = self._reduce(term[2], limit)
			return term, response

		elif term[0] == 2:
			if term[1][0] == 1:  # Left side is an Abs
				# Beta-reduction is done using the alpha-conversion
				#   function. Here, a variable conflict would cause
				#   an abstraction's parameter to be a non-variable,
				#   which is nonsense. 
				reduced = self.alpha(term[1][2], term[1][1], term[2])
				return reduced, 1
			
			elif term[1][0] == 3 and limit == 2:
				if limit == 2:
					# Creates a temporary variable with the identical name,
					#   records its name for a later step.
					var_convert = [0, term[1][1]]
					self._nam_name = term[1][1]
					return [2, var_convert, term[2]], 2

			# If beta-reduction cannot be done, function propagates to 
			#   left and right side. Makes sure at most one reduction
			#   is done at once.
			term[1], response = self._reduce(term[1], limit)
			if response:
				return term, response
			
			term[2], response = self._reduce(term[2], limit)
			if response:
				return term, response
			return term, 0
		
		elif term[0] == 3:
			return term, 0
			
		#return term, 0
	
	# public version of beta-reduction. Tries to first preform all
	#   possible beta-reductions, only when none are availiable will
	#   try to unpack a named term. Also returns a response code.
	def beta(self, term):
		new_term, response = self._reduce(term, 1)
		if response == 0:
			new_term, response = self._reduce(term, 2)
		
			# Named term unpacking happens here. A variable version of the
			#   nam was just inserted into the term, and will now be
			#   replaced with a term from self.named_terms.
			#   operation needs to be done from the root to prevent
			#   variable conflict.
			if response == 2:
				var_convert = [0, self._nam_name]
				unpacked_nam = self.parse(self.named_terms[self._nam_name])
				new_term = self.alpha(new_term, var_convert, unpacked_nam)
		
		return new_term, response
	
	# Will reduce a term into its normal form.
	def normalize(self, term):
		response = 1
		while response:
			yield term
			term, response = self.beta(term)
		
		yield None

# Defines specified library/libraries into a manager
# Reads libraries.txt line by line. Start of library is noted by '#'.
#   When it is encountered, and one of its aliases is in names,
#   loading is set true, all subsequent lines are defined.
def load_lib(manager, names, filename='libraries.txt'):
	loading = False
	with open(filename, encoding='utf-8') as F:
		for line in F:
			typ, *argument = line.split(' ', 1)
			if typ != '#':
				if loading and argument:
					print(typ, ':=', argument[0], end='')
					manager.define(typ, argument[0])
				continue
			
			# Start of library
			loading = False
			for alias in argument[0].split():
				if alias in names:
					print(argument[0].split()[0] + ':')
					loading = True
	print('\n')

# Functionally similar to library loading, prints only one menu.
def load_text(name, filename='text.txt'):
	loading = False
	with open(filename, encoding='utf-8') as F:
		for line in F:
			typ, *argument = line.split(' ', 1) + ['']
			#print(typ, argument)
			if typ != '#':
				if loading:
					print(line,end='')
				continue
			# If a menu has finished printing, stop loop.
			if loading:
				break
			# Start of text
			for alias in argument[0].split():
				if alias == name:
					loading = True
	# This will run if no menu has been printed yet, defaults to default.
		else:
			load_text('default')

def main():
	P = Pylambda()
	load_text('start')
	last_ran = ''

	# Main loop
	while True:
		raw = input('>')
		comm, *args = raw.split() + ['']
		
		# Command names are in lists to allow aliases
		if comm in ['import']:
			load_lib(P, args)
		
		elif comm in ['clear']:
			os.system('cls' if os.name=='nt' else 'clear')
		
		elif comm in ['define']:
			P.define(args[0], last_ran)
		
		elif comm in ['help']:
			load_text(args[0])
		
		elif comm in ['exit']:
			os._exit(0)
		
		elif args:
			last_ran = raw
			gen = P.normalize(P.parse(raw))
			response = next(gen)
			while response:
				print(P.str(response))
				response = next(gen)
			print()

if __name__ == '__main__':
	main()
