@x section  54
  if (cur_val>0) C_printf("/*%d:*/",cur_val);
  else if(cur_val<0) C_printf("/*:%d*/",-cur_val);
@y
  if (cur_val>0) C_printf("\n#%d:\n",cur_val);
  else if(cur_val<0) C_printf(\n#:%d\n",-cur_val);
@z
