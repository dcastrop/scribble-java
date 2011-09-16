/*
 * Copyright 2009-10 www.scribble.org
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */
package org.scribble.protocol.validation.rules;

import java.text.MessageFormat;

import org.scribble.common.logging.Journal;
import org.scribble.protocol.ProtocolContext;
import org.scribble.protocol.model.ModelObject;
import org.scribble.protocol.model.Protocol;
import org.scribble.protocol.model.RecBlock;
import org.scribble.protocol.model.Recursion;
import org.scribble.protocol.validation.ProtocolComponentValidatorRule;

/**
 * This class provides the validation rule for the Recursion
 * model component.
 *
 */
public class RecursionValidatorRule implements ProtocolComponentValidatorRule {

    /**
     * This method determines whether the rule is applicable
     * for the supplied model object.
     * 
     * @param obj The object to check
     * @return Whether the rule can be used to validate the
     *                 supplied model object
     */
    public boolean isSupported(ModelObject obj) {
        return (obj.getClass() == org.scribble.protocol.model.Recursion.class);
    }
    
    /**
     * This method validates the supplied model object.
     * 
     * @param context The protocol context
     * @param obj The model object being validated
     * @param logger The logger
     */
    public void validate(ProtocolContext context, ModelObject obj,
                    Journal logger) {
        Recursion elem=(Recursion)obj;
        ModelObject act=elem.getParent();
        
        if (elem.getLabel() != null) {
            boolean found=false;
            
            while (!found && act != null && !(act instanceof Protocol)) {
                
                if (act instanceof RecBlock && ((RecBlock)act).getLabel() != null
                        && ((RecBlock)act).getLabel().equals(elem.getLabel())) {
                    found = true;
                }
                
                act = act.getParent();
            }
            
            if (!found) {
                logger.error(MessageFormat.format(
                        java.util.PropertyResourceBundle.getBundle("org.scribble.protocol.Messages").getString("_NO_ENCLOSING_RECUR"),
                        elem.getLabel()), obj.getProperties());                
            }
        }
    }
}
